package cli

import (
	"encoding/xml"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const renderInputsDiagram = "flowchart LR\n  A --> B\n  click A \"https://example.test/a\" \"tip\"\n  click B \"javascript:alert(1)\"\n"

func writeFixture(t *testing.T, name, content string) string {
	t.Helper()
	path := filepath.Join(t.TempDir(), name)
	if err := os.WriteFile(path, []byte(content), 0o600); err != nil {
		t.Fatal(err)
	}
	return path
}

func TestRenderConfigFlag(t *testing.T) {
	plain, _, code := invoke(t, renderInputsDiagram, "render", "-e", "svg")
	if code != 0 || strings.Contains(plain, "stroke-width='2'") {
		t.Fatalf("classic render: %d", code)
	}
	for _, config := range []string{"look: neo\n", "look: handDrawn\nhandDrawnSeed: 3\n"} {
		checkConfiguredSVG(t, config, plain)
	}
	text, _, code := invoke(t, renderInputsDiagram, "render", "-e", "text", "-c", writeFixture(t, "config.yaml", "look: neo\n"))
	plainText, _, _ := invoke(t, renderInputsDiagram, "render", "-e", "text")
	if code != 0 || text != plainText {
		t.Error("look must not change cell output")
	}
}

func checkConfiguredSVG(t *testing.T, config, plain string) {
	t.Helper()
	cfg := writeFixture(t, "config.yaml", config)
	out, stderr, code := invoke(t, renderInputsDiagram, "render", "-e", "svg", "-c", cfg)
	var document struct {
		XMLName xml.Name `xml:"svg"`
	}
	if code != 0 || xml.Unmarshal([]byte(out), &document) != nil || out == plain {
		t.Errorf("%q must change the SVG drawing: %d %q", config, code, stderr)
	}
	if !strings.Contains(stderr, "warning[interaction/unsafe-url]") || strings.Contains(out, "javascript:") {
		t.Errorf("config must preserve unsafe URL diagnostics and exclusion: %q %s", stderr, out)
	}
}

func TestRenderConfigFlagErrors(t *testing.T) {
	missing := filepath.Join(t.TempDir(), "absent.yaml")
	if _, stderr, code := invoke(t, renderInputsDiagram, "render", "-c", missing); code != 2 || !strings.HasPrefix(stderr, "cannot read "+missing+": ") {
		t.Errorf("missing config: %d %q", code, stderr)
	}
	for _, text := range []string{"- a\n", "plain text\n", "handDrawnSeed: 4294967296\n", "a: [\n"} {
		cfg := writeFixture(t, "bad.yaml", text)
		if _, stderr, code := invoke(t, renderInputsDiagram, "render", "-c", cfg); code != 2 || !strings.HasPrefix(stderr, cfg+": invalid config: ") {
			t.Errorf("%q: %d %q", text, code, stderr)
		}
	}
}

func TestRenderIconPackFlag(t *testing.T) {
	pack := writeFixture(t, "pack.json", `{"prefix":"p","icons":{"a":{"body":"<path d='M0 0h24v24z'/>","width":24,"height":24}}}`)
	other := writeFixture(t, "other.json", `{"prefix":"q","icons":{}}`)
	plain, _, _ := invoke(t, renderInputsDiagram, "render", "-e", "svg")
	out, stderr, code := invoke(t, renderInputsDiagram, "render", "-e", "svg", "--icon-pack", pack, "--icon-pack="+other)
	if code != 0 || out != plain {
		t.Errorf("icon packs must not change a diagram without icons: %d %q", code, stderr)
	}
	bad := writeFixture(t, "bad.json", `{"prefix":`)
	invalidUTF8 := writeFixture(t, "utf8.json", "{\"prefix\":\"p\",\"icons\":{\"a\":{\"body\":\"\xff\"}}}")
	absent := filepath.Join(t.TempDir(), "absent.json")
	for _, c := range []struct {
		name   string
		args   []string
		stderr string
	}{
		{"malformed pack", []string{"render", "--icon-pack", pack, "--icon-pack", bad}, bad + ": malformed icon pack: invalid JSON at byte 10: expected a value\n"},
		{"invalid UTF-8 pack", []string{"render", "--icon-pack", invalidUTF8}, invalidUTF8 + ": malformed icon pack: invalid UTF-8\n"},
		{"missing pack", []string{"render", "--icon-pack", absent}, "cannot read " + absent + ": no such file or directory\n"},
		{"check must not take --icon-pack", []string{"check", "--icon-pack", pack, "-"}, "unknown flag --icon-pack; run emd check --help\n"},
	} {
		if _, stderr, code := invoke(t, renderInputsDiagram, c.args...); code != 2 || stderr != c.stderr {
			t.Errorf("%s: %d %q", c.name, code, stderr)
		}
	}
}

func TestRenderLinksAndInteractionDiagnostics(t *testing.T) {
	out, stderr, code := invoke(t, renderInputsDiagram, "render", "-e", "svg")
	if code != 0 || strings.Count(out, "<a ") != 1 || !strings.Contains(out, "<a href='https://example.test/a'>\n<title>tip</title>\n") || strings.Contains(out, "javascript") {
		t.Fatalf("%d\n%s", code, out)
	}
	if !strings.Contains(stderr, "warning[interaction/unsafe-url]: link URL is not allowed") {
		t.Errorf("stderr: %q", stderr)
	}
	text, _, code := invoke(t, renderInputsDiagram, "render", "-e", "text")
	if code != 0 || strings.Contains(text, "example.test") || strings.Contains(text, "<a") {
		t.Errorf("text carries a link: %q", text)
	}
}

func TestRenderRejectsInvalidSource(t *testing.T) {
	out, stderr, code := invoke(t, arrowSource, "render", "-e", "svg", "--color", "never")
	if code != 1 || out != "" || !strings.HasPrefix(stderr, "<stdin>:2:5: error[flowchart/arrow-invalid]") {
		t.Errorf("exit %d, stdout %q, stderr %q", code, out, stderr)
	}
}

func TestRenderHelpListsInputFlags(t *testing.T) {
	out, _, code := invoke(t, "", "render", "--help")
	for _, want := range []string{"[--icon-pack FILE]...", "[-c CONFIG]", "icon packs none", "config none"} {
		if code != 0 || !strings.Contains(out, want) {
			t.Errorf("help lacks %q", want)
		}
	}
}
