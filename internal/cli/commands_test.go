package cli

import (
	"bytes"
	"context"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func invoke(t *testing.T, src string, args ...string) (string, string, int) {
	t.Helper()
	var out, errout bytes.Buffer
	err := Run(context.Background(), Config{Args: args, Stdin: strings.NewReader(src), Stdout: &out, Stderr: &errout})
	if err == nil {
		return out.String(), errout.String(), 0
	}
	exit, ok := errors.AsType[*ExitError](err)
	if !ok {
		t.Fatal(err)
	}
	return out.String(), errout.String(), exit.Code
}

func TestCommandContract(t *testing.T) {
	for _, c := range []struct {
		args    []string
		code    int
		message string
	}{
		{[]string{"--version"}, 0, ""},
		{nil, 2, "Usage: emd"},
		{[]string{"render", "-e", "gif"}, 2, "invalid value gif for -e; expected one of: svg, png, text"},
		{[]string{"render", "-s", "0"}, 2, "invalid value 0 for -s; expected one of: 1..8"},
		{[]string{"render", "-s", "9"}, 2, "invalid value 9 for -s; expected one of: 1..8"},
		{[]string{"render", "-s", "-1"}, 2, "invalid value -1 for -s; expected one of: 1..8"},
		{[]string{"render", "-s", "two"}, 2, "invalid value two for -s; expected one of: 1..8"},
		{[]string{"render", "-s=2.5"}, 2, "invalid value 2.5 for -s; expected one of: 1..8"},
		{[]string{"render", "--svg-text", "outline"}, 2, "invalid value outline for --svg-text; expected one of: font, paths"},
		{[]string{"render", "-b", "red", "-e", "png"}, 2, "invalid value red for -b; expected one of: #rgb, #rrggbb"},
		{[]string{"check", "-s", "2"}, 2, "unknown flag -s; run emd check --help"},
		{[]string{"render", "--width", "999999999999999999999999"}, 2, "expected one of: non-negative integers"},
		{[]string{"render", "x", "-i", "y"}, 2, "pass input either as INPUT or with -i, not both"},
	} {
		out, stderr, code := invoke(t, "flowchart LR\nA-->B\n", c.args...)
		if code != c.code || !strings.Contains(stderr, c.message) {
			t.Fatalf("%v: %d %q %q", c.args, code, out, stderr)
		}
	}
	out, _, code := invoke(t, "", "--version")
	if code != 0 || out != "emd 0.1.0\n" {
		t.Fatal(out, code)
	}
	out, _, code = invoke(t, "flowchart LR\n  A[Start --> B\n", "check", "-")
	if code != 1 || !strings.HasPrefix(out, "<stdin>:2:4: error[flowchart/unclosed-node-bracket]:") {
		t.Fatal(out, code)
	}
}

func TestColourEnabled(t *testing.T) {
	for _, c := range []struct {
		mode     string
		terminal bool
		env      TerminalEnv
		want     bool
	}{{"always", false, TerminalEnv{NoColor: "1"}, true}, {"never", true, TerminalEnv{}, false}, {"auto", true, TerminalEnv{NoColor: "1", CLIColorForce: "1"}, false}, {"auto", false, TerminalEnv{CLIColorForce: "1", Term: "dumb"}, true}, {"auto", true, TerminalEnv{Term: "dumb"}, false}, {"auto", true, TerminalEnv{}, true}, {"auto", false, TerminalEnv{ForceColor: "1"}, true}, {"auto", false, TerminalEnv{ForceColor: "0"}, false}, {"auto", true, TerminalEnv{CLIColor: "0"}, false}} {
		if got := ColourEnabled(c.mode, c.terminal, c.env); got != c.want {
			t.Fatalf("%+v terminal=%v: got %v, want %v", c.env, c.terminal, got, c.want)
		}
	}
}

func TestRenderFiles(t *testing.T) {
	dir := t.TempDir()
	src := filepath.Join(dir, "demo.mmd")
	if err := os.WriteFile(src, []byte("flowchart LR\n A[Start] --> B{Choice}\n B -->|yes| C[Done]\n B -->|no| A\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	for _, ext := range []string{"svg", "txt"} {
		output := filepath.Join(dir, "demo."+ext)
		_, stderr, code := invoke(t, "", "render", src, "-o", output)
		if code != 0 {
			t.Fatal(stderr)
		}
		b, err := os.ReadFile(output)
		if err != nil {
			t.Fatal(err)
		}
		if ext == "svg" && (!bytes.Contains(b, []byte("graphics-document document")) || bytes.Contains(b, []byte("foreignObject"))) {
			t.Fatal(string(b))
		}
	}
}

func TestCheckEmptyAndOrder(t *testing.T) {
	dir := t.TempDir()
	_, stderr, code := invoke(t, "", "check", dir)
	if code != 2 || stderr != "no Mermaid files found in "+dir+"\n" {
		t.Fatal(code, stderr)
	}
	for _, name := range []string{"b.mmd", "a.mermaid"} {
		if err := os.WriteFile(filepath.Join(dir, name), []byte("flowchart LR\n"), 0o600); err != nil {
			t.Fatal(err)
		}
	}
	out, stderr, code := invoke(t, "", "check", dir, "--output-format", "json")
	if code != 0 || stderr != "" || strings.Index(out, "a.mermaid") > strings.Index(out, "b.mmd") {
		t.Fatal(code, out, stderr)
	}
}

func TestCheckJSONExact(t *testing.T) {
	out, stderr, code := invoke(t, "flowchart LR\n  A[Start --> B\n", "check", "-", "--output-format", "json")
	want := "{\"version\":1,\"files\":[{\"path\":\"<stdin>\",\"kind\":\"flowchart\",\"diagnostics\":[{\"code\":\"flowchart/unclosed-node-bracket\",\"severity\":\"error\",\"message\":\"node bracket [ is never closed\",\"span\":{\"start\":16,\"end\":29},\"line\":2,\"column\":4,\"end_line\":3,\"end_column\":1,\"related\":[],\"help\":\"Add the closing bracket that matches the opening bracket.\",\"fixes\":[{\"title\":\"Add the closing bracket\",\"safety\":\"unsafe\",\"edits\":[{\"span\":{\"start\":29,\"end\":29},\"new_text\":\"]\"}]}]}]}],\"summary\":{\"files\":1,\"errors\":1,\"warnings\":0,\"info\":0}}\n"
	if code != 1 || stderr != "" || out != want {
		t.Fatalf("exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
}

func TestCheckUnsupportedKindVerdict(t *testing.T) {
	out, stderr, code := invoke(t, "xychart-beta\n", "check", "-", "--output-format", "json")
	want := "{\"version\":1,\"files\":[{\"path\":\"<stdin>\",\"kind\":\"xychart\",\"diagnostics\":[]}],\"summary\":{\"files\":1,\"errors\":0,\"warnings\":0,\"info\":0}}\n"
	if code != 0 || stderr != "" || out != want {
		t.Fatalf("exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
	host := filepath.Join(t.TempDir(), "host.md")
	if err := os.WriteFile(host, []byte("# host\n\n```mermaid\nxychart-beta\n```\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	out, stderr, code = invoke(t, "", "check", host, "--output-format", "json")
	wantHost := "{\"version\":1,\"files\":[{\"path\":\"" + host + "\",\"kind\":null,\"diagnostics\":[]}],\"summary\":{\"files\":1,\"errors\":0,\"warnings\":0,\"info\":0}}\n"
	if code != 0 || stderr != "" || out != wantHost {
		t.Fatalf("exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
}

func TestRenderArgumentOrder(t *testing.T) {
	path := filepath.Join(t.TempDir(), "input.mmd")
	if err := os.WriteFile(path, []byte("flowchart LR\n A --> B\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	var previous string
	for _, args := range [][]string{{"render", "-e", "text", path}, {"render", path, "-e", "text"}, {"render", "-e", "text", "--", path}} {
		out, stderr, code := invoke(t, "", args...)
		if code != 0 || stderr != "" || (previous != "" && previous != out) {
			t.Fatalf("%v: %d %q %q", args, code, out, stderr)
		}
		previous = out
	}
}

func TestRenderColourSnapshotEnv(t *testing.T) {
	t.Setenv("TERM", "xterm-256color")
	t.Setenv("COLORTERM", "")
	t.Setenv("NO_COLOR", "1")
	t.Setenv("CLICOLOR_FORCE", "1")
	const src = "flowchart LR\n  A --> B\n"
	render := func(env TerminalEnv) string {
		var out, errout bytes.Buffer
		err := Run(context.Background(), Config{
			Args:     []string{"render", "-e", "text", "--color", "always"},
			Stdin:    strings.NewReader(src),
			Stdout:   &out,
			Stderr:   &errout,
			Terminal: env,
		})
		if err != nil || errout.Len() != 0 {
			t.Fatalf("%+v: %v %q", env, err, errout.String())
		}
		return out.String()
	}
	truecolour := render(TerminalEnv{ColorTerm: "truecolor", Term: "screen", NoColor: "1"})
	if !strings.Contains(truecolour, "\x1b[38;2;") || strings.Contains(truecolour, "\x1b[38;5;") {
		t.Fatalf("expected truecolor escapes from snapshot ColorTerm despite TERM=256color, NO_COLOR=1, CLICOLOR_FORCE=1 in the process environment: %q", truecolour)
	}
	t.Setenv("TERM", "dumb")
	t.Setenv("COLORTERM", "truecolor")
	ansi := render(TerminalEnv{ColorTerm: "", Term: "xterm-256color"})
	if !strings.Contains(ansi, "\x1b[38;5;") || strings.Contains(ansi, "\x1b[38;2;") {
		t.Fatalf("expected 256-colour escapes from snapshot TERM despite ambient TERM=dumb and COLORTERM=truecolor: %q", ansi)
	}
}
