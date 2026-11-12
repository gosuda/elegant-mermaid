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
	}{{[]string{"--version"}, 0, ""}, {nil, 2, "Usage: emd"}, {[]string{"render", "-e", "png"}, 2, "invalid value png for -e; expected one of: svg, text"}, {[]string{"render", "-s", "2"}, 2, "unknown flag -s; run emd render --help"}, {[]string{"render", "--svg-text", "paths"}, 2, "invalid value paths for --svg-text; expected one of: font"}, {[]string{"render", "--width", "999999999999999999999999"}, 2, "expected one of: non-negative integers"}, {[]string{"render", "x", "-i", "y"}, 2, "pass input either as INPUT or with -i, not both"}} {
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
func TestColourPrecedence(t *testing.T) {
	for _, c := range []struct {
		mode     string
		terminal bool
		env      map[string]string
		want     bool
	}{{"always", false, map[string]string{"NO_COLOR": "1"}, true}, {"never", true, nil, false}, {"auto", true, map[string]string{"NO_COLOR": "1", "CLICOLOR_FORCE": "1"}, false}, {"auto", false, map[string]string{"CLICOLOR_FORCE": "1", "TERM": "dumb"}, true}, {"auto", true, map[string]string{"TERM": "dumb"}, false}, {"auto", true, nil, true}} {
		if got := ColourEnabled(c.mode, c.terminal, func(k string) string { return c.env[k] }); got != c.want {
			t.Fatal(c, got)
		}
	}
}
func TestRenderFiles(t *testing.T) {
	dir := t.TempDir()
	src := filepath.Join(dir, "demo.mmd")
	if err := os.WriteFile(src, []byte("flowchart LR\n A[Start] --> B{Choice}\n B -->|yes| C[Done]\n B -->|no| A\n"), 0600); err != nil {
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
		if err := os.WriteFile(filepath.Join(dir, name), []byte("flowchart LR\n"), 0600); err != nil {
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
	want := "{\"version\":1,\"files\":[{\"path\":\"<stdin>\",\"kind\":\"flowchart\",\"diagnostics\":[{\"code\":\"flowchart/unclosed-node-bracket\",\"severity\":\"error\",\"message\":\"node bracket [ is never closed\",\"span\":{\"start\":16,\"end\":29},\"line\":2,\"column\":4,\"end_line\":3,\"end_column\":1,\"related\":[],\"help\":\"Add the closing bracket that matches the opening bracket.\",\"fixes\":[]}]}],\"summary\":{\"files\":1,\"errors\":1,\"warnings\":0,\"info\":0}}\n"
	if code != 1 || stderr != "" || out != want {
		t.Fatalf("exit=%d stdout=%q stderr=%q", code, out, stderr)
	}
}

func TestRenderArgumentOrder(t *testing.T) {
	path := filepath.Join(t.TempDir(), "input.mmd")
	if err := os.WriteFile(path, []byte("flowchart LR\n A --> B\n"), 0600); err != nil {
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
