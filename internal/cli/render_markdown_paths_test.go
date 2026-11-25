package cli

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func markdownSymlink(t *testing.T, target, path string) {
	t.Helper()
	if err := os.Symlink(target, path); err != nil {
		t.Fatal(err)
	}
}

func TestRenderMarkdownArtifactSymlinkPrecedesParent(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{
		"input.md":           markdownTwoBlocks(),
		"assets/input-1.svg": "unrelated asset",
		"releases/v1/keep":   "existing release",
	}))
	markdownSymlink(t, "releases/v1", "current")
	requireMarkdownSuccess(t, "render", "input.md", "-a", "current/../assets", "-e", "svg")
	requireMarkdownText(t, "assets/input-1.svg", "unrelated asset")
	for _, name := range []string{"input-1.svg", "input-2.svg"} {
		if !strings.HasPrefix(readText(t, "releases/assets/"+name), "<svg") {
			t.Fatalf("asset %s did not follow the filesystem path", name)
		}
	}
}

func TestRenderMarkdownHostLinksFollowDirectorySymlinks(t *testing.T) {
	for _, host := range []string{"current/out.md", "current/../out.md"} {
		t.Run(host, func(t *testing.T) {
			t.Chdir(writeLintFiles(t, map[string]string{
				"input.md":         "```mermaid\n" + markdownFirst + "```\n",
				"releases/v1/keep": "existing release",
				"out.md":           "unrelated host",
			}))
			markdownSymlink(t, "releases/v1", "current")
			requireMarkdownSuccess(t, "render", "input.md", "-o", host, "-a", "assets")
			want := "![diagram](../../assets/out-1.svg)\n"
			if strings.Contains(host, "..") {
				want = "![diagram](../assets/out-1.svg)\n"
			}
			requireMarkdownText(t, host, want)
			requireMarkdownText(t, "out.md", "unrelated host")
		})
	}
}

func TestRenderMarkdownDefaultAssetsKeepHostDirectoryOrder(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{
		"input.md":             "```mermaid\n" + markdownFirst + "```\n",
		"releases/v1/keep":     "existing release",
		"out.assets/out-1.svg": "unrelated asset",
	}))
	markdownSymlink(t, "releases/v1", "current")
	requireMarkdownSuccess(t, "render", "input.md", "-o", "current/../out.md")
	requireMarkdownText(t, "releases/out.md", "![diagram](out.assets/out-1.svg)\n")
	requireMarkdownText(t, "out.assets/out-1.svg", "unrelated asset")
	if !strings.HasPrefix(readText(t, "releases/out.assets/out-1.svg"), "<svg") {
		t.Fatal("default asset directory did not follow the host")
	}
}

func TestRenderMarkdownUnusedImageParentIsNotProbed(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"input.md": markdownTwoBlocks(), "report": "unrelated file"}))
	requireMarkdownSuccess(t, "render", "input.md", "-o", "report/diagram.svg", "-a", "assets")
	requireMarkdownText(t, "report", "unrelated file")
	if !strings.HasPrefix(readText(t, "assets/diagram-1.svg"), "<svg") {
		t.Fatal("image basename was not retained")
	}
}

func TestRenderMarkdownDotfileImagesInferFormat(t *testing.T) {
	for _, tc := range []struct{ output, prefix string }{
		{".svg", "<svg"}, {".png", "\x89PNG\r\n\x1a\n"}, {".txt", ""},
	} {
		t.Run(tc.output, func(t *testing.T) {
			t.Chdir(writeLintFiles(t, map[string]string{"input.md": "```mermaid\n" + markdownFirst + "```\n"}))
			requireMarkdownSuccess(t, "render", "input.md", "-o", tc.output, "--color", "never")
			got := readText(t, tc.output+"-1")
			if got == "" || !strings.HasPrefix(got, tc.prefix) {
				t.Fatalf("unexpected artifact bytes: %q", got)
			}
		})
	}
}

func TestRenderMarkdownMissingDirectoriesAndFinalSymlinks(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{
		"input.md": "```mermaid\n" + markdownFirst + "```\n",
		"sentinel": "unrelated file",
	}))
	if err := os.Mkdir("assets", 0o755); err != nil {
		t.Fatal(err)
	}
	markdownSymlink(t, "../sentinel", "assets/out-1.svg")
	requireMarkdownSuccess(t, "render", "input.md", "-o", "docs/missing/../out.md", "-a", "assets/missing/..")
	requireMarkdownText(t, "docs/out.md", "![diagram](../assets/out-1.svg)\n")
	requireMarkdownText(t, "sentinel", "unrelated file")
	info, err := os.Lstat("assets/out-1.svg")
	if err != nil || !info.Mode().IsRegular() {
		t.Fatalf("final output symlink was not replaced: %v, %v", info, err)
	}
}

func TestRenderMarkdownInvalidDirectoryComponentsPreserveOutputs(t *testing.T) {
	for _, directory := range []string{"file/..", "dangling/.."} {
		t.Run(directory, func(t *testing.T) {
			t.Chdir(writeLintFiles(t, map[string]string{
				"input.md": "```mermaid\n" + markdownFirst + "```\n",
				"file":     "regular file",
				"out.md":   "existing host",
			}))
			markdownSymlink(t, "absent", "dangling")
			out, stderr, code := invoke(t, "", "render", "input.md", "-o", "out.md", "-a", directory)
			if code != 2 || out != "" || !strings.HasPrefix(stderr, "cannot write out.md:") {
				t.Fatalf("invalid parent: exit=%d stdout=%q stderr=%q", code, out, stderr)
			}
			requireMarkdownText(t, "out.md", "existing host")
			requireMarkdownAbsent(t, "out-1.svg", filepath.Join("absent", "out-1.svg"))
		})
	}
}

func TestRenderMarkdownMissingPrefixStillResolvesLaterSymlinks(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{
		"input.md":         "```mermaid\n" + markdownFirst + "```\n",
		"releases/v1/keep": "existing release",
	}))
	markdownSymlink(t, "releases/v1", "current")
	requireMarkdownSuccess(t, "render", "input.md", "-o", "missing/../current/../out.md", "-a", "assets")
	requireMarkdownText(t, "releases/out.md", "![diagram](../assets/out-1.svg)\n")
	requireMarkdownSuccess(t, "render", "input.md", "-o", "docs/out.md", "-a", "another/../current/../pictures")
	requireMarkdownText(t, "docs/out.md", "![diagram](../releases/pictures/out-1.svg)\n")
	if !strings.HasPrefix(readText(t, "releases/pictures/out-1.svg"), "<svg") {
		t.Fatal("asset path did not resolve the later symlink")
	}
}

func TestRenderMarkdownMissingPrefixStillRejectsLaterFile(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{
		"input.md": "```mermaid\n" + markdownFirst + "```\n",
		"file":     "regular file",
		"out.md":   "existing host",
	}))
	out, stderr, code := invoke(t, "", "render", "input.md", "-o", "out.md", "-a", "missing/../file/images")
	if code != 2 || out != "" || stderr != "cannot write out.md: not a directory\n" {
		t.Fatalf("later file: exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	requireMarkdownText(t, "out.md", "existing host")
	requireMarkdownAbsent(t, "missing")
}
