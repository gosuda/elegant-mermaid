package cli

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func markdownWindowsDirectory(t *testing.T) string {
	t.Helper()
	base := writeLintFiles(t, map[string]string{
		"input.md": "~~~mermaid\n" + markdownFirst + "~~~\n",
	})
	literal := "\\\\?\\" + base
	if strings.HasPrefix(base, "\\\\") {
		literal = "\\\\?\\UNC\\" + base[2:]
	}
	t.Cleanup(func() {
		if err := os.RemoveAll(literal); err != nil {
			t.Error(err)
		}
	})
	t.Chdir(base)
	return literal
}

func requireMarkdownWindowsImage(t *testing.T, path string) {
	t.Helper()
	if !strings.HasPrefix(readText(t, path), "<svg") {
		t.Fatalf("expected native image at %q", path)
	}
}

func TestMarkdownWindowsDirectorySpellings(t *testing.T) {
	for _, tc := range []struct {
		name, operand, actual, url string
		literal, exists            bool
	}{
		{"ordinary-dot", "assets.", "assets", "assets", false, true},
		{"ordinary-space", "assets ", "assets", "assets", false, true},
		{"prospective-dot", "future.", "future", "future", false, false},
		{"literal-dot", "assets.", "assets.", "assets.", true, true},
		{"literal-space", "assets ", "assets ", "assets%20", true, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			base := markdownWindowsDirectory(t)
			actual := base + "\\" + tc.actual
			if tc.exists {
				if err := os.Mkdir(actual, 0o755); err != nil {
					t.Fatal(err)
				}
			}
			operand := tc.operand
			if tc.literal {
				operand = base + "\\" + operand
			}
			requireMarkdownSuccess(t, "render", "input.md", "-o", "report.md", "-a", operand)
			requireMarkdownText(t, "report.md", "![diagram]("+tc.url+"/report-1.svg)\n")
			requireMarkdownWindowsImage(t, actual+"\\report-1.svg")
		})
	}
}

func TestMarkdownWindowsMixedPrefixes(t *testing.T) {
	for _, literalHost := range []bool{false, true} {
		t.Run(map[bool]string{false: "literal-assets", true: "literal-host"}[literalHost], func(t *testing.T) {
			base := markdownWindowsDirectory(t)
			if err := os.Mkdir("assets", 0o755); err != nil {
				t.Fatal(err)
			}
			host, assets := "report.md", base+"\\assets"
			if literalHost {
				host, assets = base+"\\report.md", "assets"
			}
			requireMarkdownSuccess(t, "render", "input.md", "-o", host, "-a", assets)
			requireMarkdownText(t, "report.md", "![diagram](assets/report-1.svg)\n")
			requireMarkdownWindowsImage(t, base+"\\assets\\report-1.svg")
		})
	}
}

func TestMarkdownWindowsSymlinkRetainsLiteralAncestor(t *testing.T) {
	for _, suffix := range []string{" ", "."} {
		t.Run(map[string]string{" ": "space", ".": "dot"}[suffix], func(t *testing.T) {
			base := markdownWindowsDirectory(t)
			target := base + "\\literal" + suffix
			markdownWindowsLiteralLink(t, target)
			requireMarkdownSuccess(t, "render", "input.md", "-o", "report.md", "-a", "linked")
			escaped := strings.ReplaceAll(suffix, " ", "%20")
			requireMarkdownText(t, "report.md", "![diagram](literal"+escaped+"/report-1.svg)\n")
			requireMarkdownWindowsImage(t, target+"\\report-1.svg")
			requireMarkdownSuccess(t, "render", "input.md", "-o", "child.md", "-a", "linked\\child.")
			requireMarkdownText(t, "child.md", "![diagram](literal"+escaped+"/child/child-1.svg)\n")
			requireMarkdownWindowsImage(t, target+"\\child\\child-1.svg")
			requireMarkdownText(t, "literal/report-1.svg", "unrelated image")
		})
	}
}

func markdownWindowsLiteralLink(t *testing.T, target string) {
	t.Helper()
	if err := os.Mkdir(target, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir(target+"\\child", 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.Mkdir("literal", 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile("literal/report-1.svg", []byte("unrelated image"), 0o644); err != nil {
		t.Fatal(err)
	}
	markdownSymlink(t, target, "linked")
	if err := os.WriteFile("linked/native.svg", []byte("native"), 0o644); err != nil {
		t.Fatal(err)
	}
	requireMarkdownText(t, target+"\\native.svg", "native")
}

func TestMarkdownWindowsFinalNamesAndLinks(t *testing.T) {
	for _, suffix := range []string{".", " "} {
		t.Run(map[string]string{".": "dot", " ": "space"}[suffix], func(t *testing.T) {
			base := markdownWindowsDirectory(t)
			literal := base + "\\image.svg" + suffix
			if err := commitMarkdownOutputs([]markdownOutput{{path: "image.svg" + suffix, data: []byte("ordinary")}}); err != nil {
				t.Fatal(err)
			}
			requireMarkdownText(t, base+"\\image.svg", "ordinary")
			if err := commitMarkdownOutputs([]markdownOutput{{path: literal, data: []byte("literal")}}); err != nil {
				t.Fatal(err)
			}
			requireMarkdownText(t, literal, "literal")
			requireMarkdownText(t, base+"\\image.svg", "ordinary")
		})
	}
}

func TestMarkdownWindowsFinalLinkIsReplaced(t *testing.T) {
	base := markdownWindowsDirectory(t)
	sentinel := filepath.Join(base, "sentinel")
	if err := os.WriteFile(sentinel, []byte("untouched"), 0o644); err != nil {
		t.Fatal(err)
	}
	markdownSymlink(t, sentinel, "image.svg")
	if err := commitMarkdownOutputs([]markdownOutput{{path: "image.svg", data: []byte("replacement")}}); err != nil {
		t.Fatal(err)
	}
	requireMarkdownText(t, sentinel, "untouched")
	requireMarkdownText(t, "image.svg", "replacement")
	info, err := os.Lstat("image.svg")
	if err != nil || !info.Mode().IsRegular() {
		t.Fatalf("final entry was followed instead of replaced: %v, %v", info, err)
	}
}

func TestMarkdownWindowsNamespaceNormalization(t *testing.T) {
	for _, tc := range []struct {
		name, prefix, operand, actual, url string
	}{
		{"ordinary-dot-final", "", "assets.", "assets", "assets"},
		{"ordinary-dot-intermediate", "", "assets.\\child", "assets\\child", "assets/child"},
		{"ordinary-space-final", "", "assets ", "assets", "assets"},
		{"ordinary-space-intermediate", "", "assets \\child", "assets \\child", "assets%20/child"},
		{"device-dot-final", "\\\\.\\", "assets.", "assets", "assets"},
		{"device-dot-intermediate", "\\\\.\\", "assets.\\child", "assets\\child", "assets/child"},
		{"device-space-final", "\\\\.\\", "assets ", "assets", "assets"},
		{"device-space-intermediate", "\\\\.\\", "assets \\child", "assets \\child", "assets%20/child"},
		{"verbatim-dot-final", "\\\\?\\", "assets.", "assets.", "assets."},
		{"verbatim-dot-intermediate", "\\\\?\\", "assets.\\child", "assets.\\child", "assets./child"},
		{"verbatim-space-final", "\\\\?\\", "assets ", "assets ", "assets%20"},
		{"verbatim-space-intermediate", "\\\\?\\", "assets \\child", "assets \\child", "assets%20/child"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			base := markdownWindowsDirectory(t)
			for _, name := range []string{"assets", "assets.", "assets "} {
				if err := os.Mkdir(base+"\\"+name, 0o755); err != nil {
					t.Fatal(err)
				}
				if err := os.Mkdir(base+"\\"+name+"\\child", 0o755); err != nil {
					t.Fatal(err)
				}
			}
			root := strings.TrimPrefix(base, "\\\\?\\")
			if tc.prefix == "" && strings.HasPrefix(root, "UNC\\") {
				root = "\\\\" + root[len("UNC\\"):]
			}
			operand := tc.prefix + root + "\\" + tc.operand
			resolved, err := resolvedOutputDirectory(operand)
			if err != nil {
				t.Fatal(err)
			}
			actual, err := os.Stat(resolved)
			if err != nil {
				t.Fatal(err)
			}
			expected, err := os.Stat(base + "\\" + tc.actual)
			if err != nil {
				t.Fatal(err)
			}
			if !os.SameFile(actual, expected) {
				t.Fatalf("directory identity for %q: got %q, want %q", operand, resolved, tc.actual)
			}
			requireMarkdownSuccess(t, "render", "input.md", "-o", "report.md", "-a", operand)
			requireMarkdownText(t, "report.md", "![diagram]("+tc.url+"/report-1.svg)\n")
			requireMarkdownWindowsImage(t, base+"\\"+tc.actual+"\\report-1.svg")
		})
	}
}
