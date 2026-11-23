package cli

import (
	"fmt"
	"os"
	"strings"
	"testing"
)

const markdownFirst = "flowchart LR\nA --> B\n"
const markdownSecond = "flowchart TD\nC --> D\n"

func markdownTwoBlocks() string {
	return "Before\n```mermaid\n" + markdownFirst + "```\nBetween\n~~~mmd\n" + markdownSecond + "~~~\nAfter\n"
}

func requireMarkdownSuccess(t *testing.T, args ...string) {
	t.Helper()
	out, stderr, code := invoke(t, "", args...)
	if code != 0 || out != "" || stderr != "" {
		t.Fatalf("%v: exit=%d stdout=%q stderr=%q", args, code, out, stderr)
	}
}

func requireMarkdownAbsent(t *testing.T, paths ...string) {
	t.Helper()
	for _, path := range paths {
		if _, err := os.Stat(path); !os.IsNotExist(err) {
			t.Fatalf("unexpected output %s: %v", path, err)
		}
	}
}

func requireMarkdownText(t *testing.T, path, want string) {
	t.Helper()
	if got := readText(t, path); got != want {
		t.Fatalf("%s = %q, want %q", path, got, want)
	}
}

func TestRenderMarkdownImageOutputsMatchStandalone(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"input.md": markdownTwoBlocks()}))
	requireMarkdownSuccess(t, "render", "input.md", "-o", "diagram.svg", "--color", "never")
	requireMarkdownAbsent(t, "diagram.svg")
	for i, source := range []string{markdownFirst, markdownSecond} {
		want, stderr, code := invoke(t, source, "render", "-e", "svg", "--color", "never")
		if code != 0 || stderr != "" {
			t.Fatalf("standalone block: %d %q", code, stderr)
		}
		requireMarkdownText(t, fmt.Sprintf("diagram-%d.svg", i+1), want)
	}
}

func TestRenderMarkdownArtifactDirectoryAndImageName(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"input.md": markdownTwoBlocks()}))
	requireMarkdownSuccess(t, "render", "input.md", "-a", "nested/assets", "-e", "text", "--color", "never")
	for _, path := range []string{"nested/assets/input-1.txt", "nested/assets/input-2.txt"} {
		if readText(t, path) == "" {
			t.Fatalf("empty artifact %s", path)
		}
	}
	requireMarkdownSuccess(t, "render", "input.md", "-o", "unused/picture.dat", "-a", "actual", "-e", "svg")
	requireMarkdownAbsent(t, "unused")
	for _, path := range []string{"actual/picture-1.dat", "actual/picture-2.dat"} {
		if !strings.HasPrefix(readText(t, path), "<svg") {
			t.Fatalf("artifact %s is not SVG", path)
		}
	}
	requireMarkdownSuccess(t, "render", "input.md", "--a=", "-e", "svg")
	if !strings.HasPrefix(readText(t, "input-1.svg"), "<svg") || !strings.HasPrefix(readText(t, "input-2.svg"), "<svg") {
		t.Fatal("empty directory did not select the current directory")
	}
}

func TestRenderMarkdownHostPreservesRawBytesAndContainers(t *testing.T) {
	const before = "Before\xff\r\n> - ```mermaid\r\n>   flowchart LR\r\n>   accTitle: Title [safe] & more!\r\n>   A --> B\r\n>   ```\r\nForeign\xfe\r\n```rust\nlet x = 1;\n```\n~~~mmd\nflowchart LR\nC --> D\n~~~\nAfter\n"
	const after = "Before\xff\r\n> - ![Title \\[safe\\] \\& more\\!](published.assets/published-1.svg)\r\nForeign\xfe\r\n```rust\nlet x = 1;\n```\n![diagram](published.assets/published-2.svg)\nAfter\n"
	for _, suffix := range []string{"md", "markdown", "mdx"} {
		t.Run(suffix, func(t *testing.T) {
			input, output := "input."+suffix, "reports/published."+suffix
			t.Chdir(writeLintFiles(t, map[string]string{input: before}))
			requireMarkdownSuccess(t, "render", input, "-o", output, "--color", "never")
			requireMarkdownText(t, output, after)
			requireMarkdownText(t, input, before)
			for _, path := range []string{"reports/published.assets/published-1.svg", "reports/published.assets/published-2.svg"} {
				if !strings.HasPrefix(readText(t, path), "<svg") {
					t.Fatalf("artifact %s is not SVG", path)
				}
			}
		})
	}
}

func TestRenderMarkdownDotfileHostsKeepStem(t *testing.T) {
	for _, name := range []string{".md", ".markdown", ".mdx"} {
		t.Run(name, func(t *testing.T) {
			t.Chdir(writeLintFiles(t, map[string]string{name: "```mermaid\n" + markdownFirst + "```\n"}))
			requireMarkdownSuccess(t, "render", name, "-a", "assets")
			if !strings.HasPrefix(readText(t, "assets/"+name+"-1.svg"), "<svg") {
				t.Fatal("dotfile stem was lost")
			}
		})
	}
}

func TestRenderMarkdownRelativeEncodedLinks(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"input.md": "```mermaid\n" + markdownFirst + "```\n"}))
	requireMarkdownSuccess(t, "render", "input.md", "-o", "docs/renamed.md", "-a", "assets/a b#%()é")
	requireMarkdownText(t, "docs/renamed.md", "![diagram](../assets/a%20b%23%25%28%29%C3%A9/renamed-1.svg)\n")
	if !strings.HasPrefix(readText(t, "assets/a b#%()é/renamed-1.svg"), "<svg") {
		t.Fatal("encoded link does not name an SVG artifact")
	}
}

func TestRenderMarkdownUnclosedBlockLineEndings(t *testing.T) {
	for _, tc := range []struct{ name, before, after string }{
		{"colon lone CR", "Before\n> :::mermaid\n> flowchart LR\r> A --> B\rAfter\n", "Before\n> ![diagram](out.assets/out-1.svg)\rAfter\n"},
		{"indented quote CRLF", "Before\n  > ```mermaid\r\n  > flowchart LR\r\n  > A --> B\r\nAfter\n", "Before\n  > ![diagram](out.assets/out-1.svg)\r\nAfter\n"},
		{"EOF", "Before\n```mermaid\nflowchart LR\nA --> B", "Before\n![diagram](out.assets/out-1.svg)"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			t.Chdir(writeLintFiles(t, map[string]string{"input.md": tc.before}))
			requireMarkdownSuccess(t, "render", "input.md", "-o", "out.md")
			requireMarkdownText(t, "out.md", tc.after)
		})
	}
}

func TestRenderMarkdownHostSupportsPNG(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"input.md": "```mermaid\n" + markdownFirst + "```\n"}))
	requireMarkdownSuccess(t, "render", "input.md", "-o", "out.mdx", "-e", "png", "-s", "1")
	requireMarkdownText(t, "out.mdx", "![diagram](out.assets/out-1.png)\n")
	if !strings.HasPrefix(readText(t, "out.assets/out-1.png"), "\x89PNG\r\n\x1a\n") {
		t.Fatal("PNG artifact has no PNG signature")
	}
}

func TestRenderMarkdownUsageErrors(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"input.md": markdownTwoBlocks(), "single.mmd": markdownFirst}))
	for _, tc := range []struct {
		args []string
		want string
	}{
		{[]string{"render", "input.md"}, "rendering Markdown input requires -o OUTPUT or -a ARTEFACT_DIR\n"},
		{[]string{"render", "single.mmd", "-a", "assets"}, "-a requires Markdown input\n"},
		{[]string{"render", "single.mmd", "--a="}, "-a requires Markdown input\n"},
		{[]string{"render", "input.md", "-o", "out.md", "-e", "text"}, "invalid value text for -e; expected one of: svg, png\n"},
	} {
		out, stderr, code := invoke(t, "", tc.args...)
		if code != 2 || out != "" || stderr != tc.want {
			t.Errorf("%v: exit=%d stdout=%q stderr=%q", tc.args, code, out, stderr)
		}
	}
	requireMarkdownAbsent(t, "assets", "out.md")
}

func TestRenderMarkdownZeroBlocksWritesNothing(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"empty.md": "prose\n```rust\nlet x = 1;\n```\n"}))
	out, stderr, code := invoke(t, "", "render", "empty.md", "-o", "absent/out.md")
	if code != 1 || out != "" || stderr != "no Mermaid blocks found in empty.md; add a fenced code block labelled mermaid\n" {
		t.Fatalf("zero blocks: exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	requireMarkdownAbsent(t, "absent")
}

func TestRenderMarkdownLaterParseErrorWritesNothing(t *testing.T) {
	bad := "```mermaid\n" + markdownFirst + "```\n```mermaid\nflowchart LR\nC -> D\n```\n"
	t.Chdir(writeLintFiles(t, map[string]string{"bad.md": bad, "out-1.svg": "existing asset"}))
	out, stderr, code := invoke(t, "", "render", "bad.md", "-o", "out.svg", "--color", "never")
	if code != 1 || out != "" || !strings.Contains(stderr, "bad.md:7:3: error[flowchart/arrow-invalid]") {
		t.Fatalf("later error: exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	requireMarkdownText(t, "out-1.svg", "existing asset")
	requireMarkdownAbsent(t, "out-2.svg")
}

func TestRenderMarkdownMapsAllSourceDiagnostics(t *testing.T) {
	const host = "# hé😀\n\n> - ```mermaid\n>   flowchart LR\n>   A -> B\n>   ```\n\n:::mermaid\nflowchart LR\nC -> D\n:::\n"
	t.Chdir(writeLintFiles(t, map[string]string{"bad.md": host}))
	checked, _, checkedCode := invoke(t, "", "check", "bad.md", "--color", "never")
	out, stderr, code := invoke(t, "", "render", "bad.md", "-o", "out.svg", "--color", "never")
	if checkedCode != 1 || code != 1 || out != "" || stderr != checked {
		t.Fatalf("mapped diagnostics: check=%d render=%d stdout=%q stderr=%q want=%q", checkedCode, code, out, stderr, checked)
	}
	requireMarkdownAbsent(t, "out-1.svg")
}

func TestRenderMarkdownRejectsInvalidBlockBytes(t *testing.T) {
	const host = "Before\xff\n> ```mermaid\n> flowchart LR\n> %% bad \xfe\n> A --> B\n> ```\n"
	t.Chdir(writeLintFiles(t, map[string]string{"invalid.md": host}))
	out, stderr, code := invoke(t, "", "render", "invalid.md", "-o", "out.md", "--color", "never")
	if code != 1 || out != "" || !strings.Contains(stderr, "invalid.md:4:10: error[source/invalid-utf8]") {
		t.Fatalf("invalid block: exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	if strings.Count(stderr, "error[source/invalid-utf8]") != 1 {
		t.Fatalf("invalid prose created a block error: %q", stderr)
	}
	requireMarkdownAbsent(t, "out.md", "out.assets")
}

func TestRenderMarkdownLimitsCountOnlyBlockBytes(t *testing.T) {
	host := strings.Repeat("prose ", 100) + "\n```mermaid\n" + markdownFirst + "```\n"
	t.Chdir(writeLintFiles(t, map[string]string{"input.md": host, "config.yaml": "maxTextSize: 30\n"}))
	requireMarkdownSuccess(t, "render", "input.md", "-o", "out.svg", "-c", "config.yaml")
	if !strings.HasPrefix(readText(t, "out-1.svg"), "<svg") {
		t.Fatal("block below source cap was not rendered")
	}
}

func TestRenderMarkdownLaterLayoutErrorWritesNothing(t *testing.T) {
	const overflow = "pie\n\"A\" : 99999999999\n"
	_, want, standaloneCode := invoke(t, overflow, "render", "-e", "svg")
	if standaloneCode != 1 || want != "arithmetic overflow\n" {
		t.Fatalf("standalone overflow: exit=%d stderr=%q", standaloneCode, want)
	}
	bad := "```mermaid\n" + markdownFirst + "```\n```mermaid\n" + overflow + "```\n"
	t.Chdir(writeLintFiles(t, map[string]string{"bad.md": bad, "out-1.svg": "existing asset"}))
	out, stderr, code := invoke(t, "", "render", "bad.md", "-o", "out.svg")
	if code != 1 || out != "" || stderr != want {
		t.Fatalf("later layout error: exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	requireMarkdownText(t, "out-1.svg", "existing asset")
	requireMarkdownAbsent(t, "out-2.svg")
}
