package cli

import (
	"errors"
	"path/filepath"
	"strings"
	"testing"
)

func TestLintFixPreservesMarkdownHostBytes(t *testing.T) {
	for _, tc := range []struct{ name, before, after string }{
		{"prose", "Caf\xe9\n", "Caf\xe9\n"},
		{"clean", "Caf\xe9\n```mermaid\nflowchart LR\nA --> B\n```\nTail\xff\n", "Caf\xe9\n```mermaid\nflowchart LR\nA --> B\n```\nTail\xff\n"},
		{"fixed", "Caf\xe9\r\n```mermaid\r\nflowchart LR\r\n%% \xe2\x82\r\nA -> B\r\n```\r\nTail\xff\r\n", "Caf\xe9\r\n```mermaid\r\nflowchart LR\r\n%% \uFFFD\r\nA --> B\r\n```\r\nTail\xff\r\n"},
		{"nested", "Prose\xff\n> - Notes\n>   ```mermaid \xfe\n>   flowchart LR\n>   %% \xe2\x82\n>   A -> B\n>   ```\nTail\xff\n", "Prose\xff\n> - Notes\n>   ```mermaid \xfe\n>   flowchart LR\n>   %% \uFFFD\n>   A --> B\n>   ```\nTail\xff\n"},
		{"empty", "Prose\xff\n```mermaid\n```\n", "Prose\xff\n```mermaid\n```\n"},
		{"unclosed", "Prose\xff\n```mermaid\nflowchart LR\nA -> B", "Prose\xff\n```mermaid\nflowchart LR\nA --> B"},
		{"foreign", "```text\nCaf\xe9\n```\n", "```text\nCaf\xe9\n```\n"},
		{"multiple", "Before\xff\n```mermaid\nflowchart LR\nA -> B\n```\nBetween\xe2\x82\n~~~mmd\nflowchart LR\nC -> D\n~~~\nAfter\xfe\n", "Before\xff\n```mermaid\nflowchart LR\nA --> B\n```\nBetween\xe2\x82\n~~~mmd\nflowchart LR\nC --> D\n~~~\nAfter\xfe\n"},
		{"container-exit", "Before\xff\n> ```mermaid\n> flowchart LR\n> A -> B\nAfter\xe9\n", "Before\xff\n> ```mermaid\n> flowchart LR\n> A --> B\nAfter\xe9\n"},
		{"indented-quote", "Before\xff\n  > ```mermaid\n  > flowchart LR\n  > %% \xe2\x82\n  > A -> B\n  > ```\nAfter\xfe\n", "Before\xff\n  > ```mermaid\n  > flowchart LR\n  > %% \uFFFD\n  > A --> B\n  > ```\nAfter\xfe\n"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			requireFixedHostBytes(t, tc.before, tc.after)
		})
	}
}

func TestLintFixPreservesHostBytesAroundLineDeletion(t *testing.T) {
	before := "Before\xff\r\n> ```mermaid\r\n> flowchart LR\r\n>   A --> B\r\n>   end\r\n> ```\r\nAfter\xfe\r\n"
	after := "Before\xff\r\n> ```mermaid\r\n> flowchart LR\r\n>   A --> B\r\n> ```\r\nAfter\xfe\r\n"
	requireFixedHostBytes(t, before, after, "--unsafe-fixes")
}

func requireFixedHostBytes(t *testing.T, before, after string, flags ...string) {
	t.Helper()
	dir := writeLintFiles(t, map[string]string{"document.md": before})
	path := filepath.Join(dir, "document.md")
	args := append([]string{"lint", "--fix", "--no-config", "--color", "never", path}, flags...)
	out, stderr, code := invoke(t, "", args...)
	if got := readText(t, path); got != after {
		t.Fatalf("host bytes changed: %q; want %q", got, after)
	}
	if code != 1 || stderr != "" || !strings.Contains(out, "source/invalid-utf8") {
		t.Fatalf("unfixed prose must remain diagnosed: exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	checked, checkStderr, checkCode := invoke(t, "", "lint", "--no-config", "--color", "never", path)
	if checked != out || checkStderr != stderr || checkCode != code {
		t.Fatalf("fix diagnostics do not describe the written bytes: exit=%d stdout=%q stderr=%q", checkCode, checked, checkStderr)
	}
}

func TestPreserveHostBytesRejectsProtectedChanges(t *testing.T) {
	original := []byte("Before\xff\n```mermaid\nflowchart LR\nA --> B\n```\n")
	for _, fixed := range []string{
		"Different\uFFFD\n```mermaid\nflowchart LR\nA --> B\n```\n",
		"Before\uFFFD\n```mmd\nflowchart LR\nA --> B\n```\n",
		"Before\uFFFD\n",
		"Before\uFFFD\n```mermaid\nflowchart LR\nA --> B\n```\n```mermaid\nflowchart LR\n```\n",
	} {
		got, err := preserveHostBytes(original, []byte(fixed))
		if !errors.Is(err, errHostFixBoundaries) || got != nil {
			t.Fatalf("protected change must fail without output: result=%q err=%v", got, err)
		}
	}
}

func TestPreserveHostBytesAllowsEmptyBody(t *testing.T) {
	original := []byte("Before\xff\n```mermaid\nend\n```\nAfter\xfe\n")
	fixed := []byte("Before\uFFFD\n```mermaid\n```\nAfter\uFFFD\n")
	want := "Before\xff\n```mermaid\n```\nAfter\xfe\n"
	got, err := preserveHostBytes(original, fixed)
	if err != nil || string(got) != want {
		t.Fatalf("empty body: result=%q err=%v; want %q", got, err, want)
	}
}
