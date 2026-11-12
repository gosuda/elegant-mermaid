package cli

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

type hostCheckSpan struct{ Start, End int }
type hostCheckEdit struct {
	Span    hostCheckSpan `json:"span"`
	NewText string        `json:"new_text"`
}
type hostCheckDiagnostic struct {
	Code   string        `json:"code"`
	Span   hostCheckSpan `json:"span"`
	Line   int           `json:"line"`
	Column int           `json:"column"`
	Fixes  []struct {
		Edits []hostCheckEdit `json:"edits"`
	} `json:"fixes"`
}
type hostCheckFile struct {
	Path        string                `json:"path"`
	Diagnostics []hostCheckDiagnostic `json:"diagnostics"`
}

func writeHostFixture(t *testing.T, path, text string) {
	t.Helper()
	if err := os.WriteFile(path, []byte(text), 0600); err != nil {
		t.Fatal(err)
	}
}

func checkHostJSON(t *testing.T, path string, count int) []hostCheckFile {
	t.Helper()
	out, stderr, code := invoke(t, "", "check", path, "--output-format", "json")
	if code != 1 || stderr != "" {
		t.Fatalf("exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	var document struct {
		Files []hostCheckFile `json:"files"`
	}
	if err := json.Unmarshal([]byte(out), &document); err != nil {
		t.Fatal(err)
	}
	if len(document.Files) != count {
		t.Fatalf("files: %s", out)
	}
	return document.Files
}

func onlyHostEdit(t *testing.T, d hostCheckDiagnostic) hostCheckEdit {
	t.Helper()
	if len(d.Fixes) != 1 {
		t.Fatalf("fix count: %+v", d)
	}
	if len(d.Fixes[0].Edits) != 1 {
		t.Fatalf("edit count: %+v", d)
	}
	return d.Fixes[0].Edits[0]
}

func TestCheckMarkdownHosts(t *testing.T) {
	dir := t.TempDir()
	bad := "Heading\n\n> ```mermaid\n> flowchart LR\n>   A[Start --> B\n> ```\n\n```mermaid\nflowchart LR\n  C[Broken --> D\n```\n"
	for _, ext := range []string{".md", ".markdown", ".mdx"} {
		path := filepath.Join(dir, "broken"+ext)
		writeHostFixture(t, path, bad)
		assertMalformedHostPositions(t, path)
	}
	clean := filepath.Join(dir, "clean.md")
	writeHostFixture(t, clean, "Prose is not Mermaid.\n```text\nnot a diagram\n```\n```mermaid\nflowchart LR\nA --> B\n```\n")
	assertCleanHost(t, clean)
	prose := filepath.Join(t.TempDir(), "prose.md")
	writeHostFixture(t, prose, "No Mermaid fences here.\n")
	assertCleanHost(t, prose)
	for _, file := range checkHostJSON(t, dir, 4) {
		if file.Path == clean {
			continue
		}
		assertBracketHostFix(t, file, bad)
	}
}

func assertMalformedHostPositions(t *testing.T, path string) {
	t.Helper()
	out, stderr, code := invoke(t, "", "check", path, "--color", "never")
	if code != 1 || stderr != "" {
		t.Fatalf("exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	for _, position := range []string{":5:6:", ":10:4:"} {
		if !strings.Contains(out, path+position+" error[flowchart/unclosed-node-bracket]") {
			t.Fatalf("host position: %q", out)
		}
	}
}

func assertCleanHost(t *testing.T, path string) {
	t.Helper()
	out, stderr, code := invoke(t, "", "check", path)
	if code != 0 || out != "" || stderr != "" {
		t.Fatalf("clean host: %d %q %q", code, out, stderr)
	}
}

func assertBracketHostFix(t *testing.T, file hostCheckFile, bad string) {
	t.Helper()
	if len(file.Diagnostics) != 2 {
		t.Fatalf("%s: %+v", file.Path, file.Diagnostics)
	}
	first := file.Diagnostics[0]
	bracket := strings.Index(bad, "[Start")
	lineEnd := bracket + strings.Index(bad[bracket:], "\n")
	if first.Span.Start != bracket {
		t.Fatalf("host span: %+v", first)
	}
	edit := onlyHostEdit(t, first)
	if edit.Span.Start != lineEnd || edit.Span.End != lineEnd {
		t.Fatalf("host edit: %+v", edit)
	}
}

func TestCheckMarkdownInvalidUTF8(t *testing.T) {
	for _, tc := range []struct{ name, raw, repaired string }{
		{"before-block", "Intro \xff\xfe\n> ```mermaid\n> flowchart LR\n> A -> B\n> ```\n", "Intro \uFFFD\uFFFD\n> ```mermaid\n> flowchart LR\n> A -> B\n> ```\n"},
		{"quoted-block", "> ```mermaid\n> flowchart LR\n> %% bad \xff\xfe\n> A -> B\n> ```\n", "> ```mermaid\n> flowchart LR\n> %% bad \uFFFD\uFFFD\n> A -> B\n> ```\n"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "host.md")
			writeHostFixture(t, path, tc.raw)
			file := checkHostJSON(t, path, 1)[0]
			assertRepairedHostDiagnostics(t, file, tc.raw, tc.repaired)
		})
	}
}

func assertRepairedHostDiagnostics(t *testing.T, file hostCheckFile, raw, repaired string) {
	t.Helper()
	if len(file.Diagnostics) != 2 {
		t.Fatalf("diagnostics: %+v", file)
	}
	ds := file.Diagnostics
	bad := strings.IndexByte(raw, 0xff)
	if ds[0].Code != "source/invalid-utf8" || ds[0].Span.Start != bad || ds[0].Span.End != bad+3 {
		t.Fatalf("UTF-8 diagnostic: %+v", ds[0])
	}
	assertRepairedArrow(t, ds[1], strings.Index(repaired, "->"))
}

func assertRepairedArrow(t *testing.T, d hostCheckDiagnostic, arrow int) {
	t.Helper()
	if d.Code != "flowchart/arrow-invalid" || d.Span.Start != arrow || d.Span.End != arrow+2 {
		t.Fatalf("mapped arrow: %+v", d)
	}
	if d.Line != 4 || d.Column != 5 {
		t.Fatalf("host position: %+v", d)
	}
	edit := onlyHostEdit(t, d)
	if edit.Span.Start != arrow || edit.Span.End != arrow+2 || edit.NewText != "-->" {
		t.Fatalf("mapped fix: %+v", edit)
	}
}
