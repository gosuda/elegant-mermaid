package tui

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestReplayKeepsGoodFrameAcrossInvalidRevision(t *testing.T) {
	dir := t.TempDir()
	bad := filepath.Join(dir, "bad.mmd")
	if err := os.WriteFile(bad, []byte("not-a-diagram\n"), 0600); err != nil {
		t.Fatal(err)
	}
	script := filepath.Join(dir, "events")
	if err := os.WriteFile(script, []byte("settle\nfile-change bad.mmd\nsettle\nkey esc\nresize 120 24\n"), 0600); err != nil {
		t.Fatal(err)
	}
	var output bytes.Buffer
	err := Replay(t.Context(), New("a.mmd", "elegant-light"), []byte("flowchart LR\n A[retained-label] --> B\n"), script, &output)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(output.String(), "retained-label") || !strings.Contains(output.String(), "STALE revision 1; latest revision 2 has errors") {
		t.Fatalf("invalid revision replaced good content or lost revision identity:\n%s", output.String())
	}
	for row := range strings.SplitSeq(strings.TrimSuffix(output.String(), "\n"), "\n") {
		if len([]rune(row)) != 120 {
			t.Fatalf("frame row has %d scalars", len([]rune(row)))
		}
	}
}

func TestReplayRejectsMalformedLineWithLocation(t *testing.T) {
	path := filepath.Join(t.TempDir(), "events")
	if err := os.WriteFile(path, []byte("# comment\nresize 19 24\n"), 0600); err != nil {
		t.Fatal(err)
	}
	var output bytes.Buffer
	err := Replay(t.Context(), New("a.mmd", "elegant-light"), []byte("flowchart LR\n A-->B\n"), path, &output)
	if err == nil || !strings.HasPrefix(err.Error(), path+":2:") || output.Len() != 0 {
		t.Fatalf("malformed replay must fail at line 2 without output: %v, %q", err, output.String())
	}
}
