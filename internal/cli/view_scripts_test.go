package cli

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

const viewFixtures = "testdata/view"

func TestViewScripts(t *testing.T) {
	cases := []struct {
		name          string
		width, height int
	}{
		{"empty", 80, 24},
		{"unknown", 80, 24},
		{"first-error", 80, 24},
		{"stale", 80, 24},
		{"oversize", 80, 24},
		{"resize", 40, 12},
		{"recreate", 80, 24},
		{"keys", 80, 24},
	}
	t.Chdir(viewFixtures)
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			want, err := os.ReadFile(c.name + ".txt")
			if err != nil {
				t.Fatal(err)
			}
			out, stderr, code := invoke(t, "", "view", c.name+".mmd", "--script", c.name+".script", "--color", "never")
			if code != 0 || stderr != "" {
				t.Fatalf("replay exit %d: %s", code, stderr)
			}
			assertViewDimensions(t, out, c.width, c.height)
			if out != string(want) {
				t.Fatalf("frame differs from %s/%s.txt:\n%s", viewFixtures, c.name, out)
			}
		})
	}
}

func writeViewInput(t *testing.T, path, text string) {
	t.Helper()
	if err := os.WriteFile(path, []byte(text), 0o600); err != nil {
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

func TestViewScriptErrors(t *testing.T) {
	dir := t.TempDir()
	writeViewInput(t, filepath.Join(dir, "good.mmd"), "flowchart LR\n A[alpha] --> B\n")
	t.Chdir(dir)
	for _, c := range []struct{ name, script, message string }{
		{"unknown verb", "bogus 1 2\n", "events.script:1: unknown verb bogus\n"},
		{"settle argument", "settle now\n", "events.script:1: settle takes no arguments\n"},
		{"delete argument", "file-delete now\n", "events.script:1: file-delete takes no arguments\n"},
		{"missing source", "file-change\n", "events.script:1: missing source path\n"},
		{"unreadable source", "file-change nothere.mmd\n", "events.script:1: cannot read nothere.mmd: no such file or directory\n"},
		{"resize arguments", "resize 80\n", "events.script:1: expected resize W H\n"},
		{"resize too small", "resize 19 24\n", "events.script:1: size requires W >= 20 and H >= 5\n"},
		{"resize overflow", "resize 99999999999999999999 24\n", "events.script:1: size requires W >= 20 and H >= 5\n"},
		{"resize not a number", "resize 80 x\n", "events.script:1: size requires W >= 20 and H >= 5\n"},
		{"empty key", "key\n", "events.script:1: invalid key\n"},
		{"long key", "key ab\n", "events.script:1: invalid key\n"},
		{"line number", "\n# comment\nbogus\n", "events.script:3: unknown verb bogus\n"},
		{"invalid UTF-8", "settle\n\xff\n", "events.script:2: invalid UTF-8\n"},
		{"invalid UTF-8 in a comment", "# \xc3(\nsettle\n", "events.script:1: invalid UTF-8\n"},
		{"invalid UTF-8 in an argument", "file-change \xff.mmd\n", "events.script:1: invalid UTF-8\n"},
		{"truncated UTF-8 before CRLF", "settle\r\n\xe2\x82\r\n", "events.script:2: invalid UTF-8\n"},
		{"earlier error first", "bogus\n\xff\n", "events.script:1: unknown verb bogus\n"},
	} {
		t.Run(c.name, func(t *testing.T) {
			writeViewInput(t, "events.script", c.script)
			out, stderr, code := invoke(t, "", "view", "good.mmd", "--script", "events.script")
			if out != "" || code != 2 || stderr != c.message {
				t.Fatalf("stdout=%q stderr=%q exit=%d; want stderr=%q exit=2", out, stderr, code, c.message)
			}
		})
	}
}

func TestViewScriptQuitSkipsInvalidUTF8(t *testing.T) {
	dir := t.TempDir()
	writeViewInput(t, filepath.Join(dir, "good.mmd"), "flowchart LR\n A[alpha] --> B\n")
	t.Chdir(dir)
	writeViewInput(t, "events.script", "settle\nkey q\n\xff\n")
	out, stderr, code := invoke(t, "", "view", "good.mmd", "--script", "events.script")
	if out == "" || stderr != "" || code != 0 {
		t.Fatalf("stdout=%q stderr=%q exit=%d; want a frame and exit 0", out, stderr, code)
	}
}

func TestViewScriptWhitespace(t *testing.T) {
	dir := t.TempDir()
	writeViewInput(t, filepath.Join(dir, "good.mmd"), "flowchart LR\n A[alpha] --> B\n")
	t.Chdir(dir)
	writeViewInput(t, "events.script", "settle\nresize  40   12 \n")
	out, stderr, code := invoke(t, "", "view", "good.mmd", "--script", "events.script")
	if code != 0 || stderr != "" {
		t.Fatalf("exit %d: %s", code, stderr)
	}
	assertViewDimensions(t, out, 40, 12)
}

func TestViewScriptReload(t *testing.T) {
	dir := t.TempDir()
	writeViewInput(t, filepath.Join(dir, "good.mmd"), "flowchart LR\n A[alpha] --> B\n")
	t.Chdir(dir)
	writeViewInput(t, "events.script", "settle\nfile-delete\nkey r\nsettle\n")
	out, stderr, code := invoke(t, "", "view", "good.mmd", "--script", "events.script")
	if code != 0 || stderr != "" {
		t.Fatalf("exit %d: %s", code, stderr)
	}
	if strings.Contains(out, "WATCH LOST") || !strings.Contains(out, "REV 2") {
		t.Fatalf("key r must read the file again and clear the lost watch:\n%s", out)
	}
}
