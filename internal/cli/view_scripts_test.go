package cli

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestViewScripts(t *testing.T) {
	good := "flowchart LR\n A[stable-label] --> B\n"
	bad := "flowchart LR\n A[broken --> B\n"
	cases := []struct {
		name, source, events string
		width, height        int
		present, absent      []string
	}{
		{name: "empty", source: "%% comment only\n", width: 80, height: 24, present: []string{"Empty diagram: add a Mermaid header"}},
		{name: "unknown", source: "unrecognised-kind\n", width: 80, height: 24, present: []string{"Diagnostics", "common/unknown-diagram-kind"}},
		{name: "first-error", source: bad, width: 80, height: 24, present: []string{"Diagnostics", "flowchart/unclosed-node-bracket"}, absent: []string{"stable-label"}},
		{name: "stale", source: good, events: "settle\nfile-change bad.mmd\nsettle\n", width: 80, height: 24, present: []string{"stable-label", "STALE revision 1;"}, absent: []string{"broken"}},
		{name: "oversize", source: "flowchart LR\n A[one]-->B[two]-->C[three]-->D[four]-->E[five]-->F[six]-->G[seven]-->H[eight]\n", width: 80, height: 24, present: []string{"pan available"}},
		{name: "resize", source: good, events: "settle\nresize 40 12\n", width: 40, height: 12, present: []string{"stable-label"}},
		{name: "watch-return", source: good, events: "settle\nfile-delete\nfile-create returned.mmd\nsettle\n", width: 80, height: 24, present: []string{"returned-label"}, absent: []string{"WATCH LOST", "stable-label"}},
		{name: "keys", source: good, events: "settle\nkey ?\n", width: 80, height: 24, present: []string{"+- Keys", "arrows, hjkl    pan", "q, Ctrl-C       quit"}},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			dir := t.TempDir()
			input := filepath.Join(dir, "diagram.mmd")
			script := filepath.Join(dir, "events")
			writeViewInput(t, input, c.source)
			writeViewInput(t, script, c.events)
			writeViewInput(t, filepath.Join(dir, "bad.mmd"), bad)
			writeViewInput(t, filepath.Join(dir, "returned.mmd"), "flowchart LR\n A[returned-label]-->B\n")
			out, stderr, code := invoke(t, "", "view", input, "--script", script, "--color", "never")
			if code != 0 || stderr != "" {
				t.Fatalf("replay exit %d: %s", code, stderr)
			}
			assertViewDimensions(t, out, c.width, c.height)
			assertViewTokens(t, out, c.present, c.absent)
		})
	}
}

func writeViewInput(t *testing.T, path, text string) {
	t.Helper()
	if err := os.WriteFile(path, []byte(text), 0600); err != nil {
		t.Fatal(err)
	}
}

func assertViewDimensions(t *testing.T, frame string, width, height int) {
	t.Helper()
	if strings.ContainsAny(frame, "\x1b\r") {
		t.Fatal("plain replay contains terminal controls")
	}
	rows := strings.Split(strings.TrimSuffix(frame, "\n"), "\n")
	if len(rows) != height {
		t.Fatalf("frame rows = %d, want %d", len(rows), height)
	}
	for i, row := range rows {
		if len([]rune(row)) != width {
			t.Fatalf("row %d width = %d, want %d", i, len([]rune(row)), width)
		}
	}
}

func assertViewTokens(t *testing.T, frame string, present, absent []string) {
	t.Helper()
	for _, token := range present {
		if !strings.Contains(frame, token) {
			t.Fatalf("frame missing %q:\n%s", token, frame)
		}
	}
	for _, token := range absent {
		if strings.Contains(frame, token) {
			t.Fatalf("frame unexpectedly contains %q:\n%s", token, frame)
		}
	}
}
