package cli_test

import (
	"bytes"
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func binaryPath(t *testing.T) string {
	t.Helper()
	path := os.Getenv("EMD_BIN")
	if path == "" {
		t.Fatal("EMD_BIN is not set; run just go-check")
	}
	return path
}

func binaryCommand(t *testing.T, args ...string) *exec.Cmd {
	t.Helper()
	ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
	t.Cleanup(cancel)
	cmd := exec.CommandContext(ctx, binaryPath(t), args...)
	cmd.Env = []string{"PATH=" + os.Getenv("PATH"), "TERM=xterm", "LC_ALL=C"}
	return cmd
}

func binaryOutput(t *testing.T, cmd *exec.Cmd, input, stdout, stderr string, code int) {
	t.Helper()
	var out, errout bytes.Buffer
	cmd.Stdin = strings.NewReader(input)
	cmd.Stdout, cmd.Stderr = &out, &errout
	err := cmd.Run()
	actual := 0
	if err != nil {
		exit, ok := err.(*exec.ExitError)
		if !ok {
			t.Fatal(err)
		}
		actual = exit.ExitCode()
	}
	if actual != code || out.String() != stdout || errout.String() != stderr {
		t.Fatalf("args=%q: exit=%d stdout=%q stderr=%q; want exit=%d stdout=%q stderr=%q", cmd.Args, actual, out.String(), errout.String(), code, stdout, stderr)
	}
}

func TestBinaryPipe(t *testing.T) {
	t.Run("cli-07", func(t *testing.T) {
		binaryOutput(t, binaryCommand(t, "render", "-e", "text", "--color", "never"), "flowchart LR\n A\n", "\n ┌───┐\n │ A │\n └───┘\n\n", "", 0)
	})
}

func TestBinaryTerminal(t *testing.T) {
	t.Run("cli-07", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
		defer cancel()
		cmd := exec.CommandContext(ctx, "script", "-qec", "\"$EMD_BIN\" render", "/dev/null")
		cmd.Env = append(os.Environ(), "EMD_BIN="+binaryPath(t))
		binaryOutput(t, cmd, "", "missing INPUT; pass a path or pipe Mermaid source\r\n", "", 2)
	})
}

func TestBinaryArgumentOrder(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "-name"), []byte("flowchart LR\n A[argument order]\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	canonical := binaryCommand(t, "render", "-e", "text", "--color", "never", "./-name")
	canonical.Dir = dir
	var stderr bytes.Buffer
	canonical.Stderr = &stderr
	want, err := canonical.Output()
	if err != nil || stderr.Len() != 0 || !bytes.Contains(want, []byte("argument order")) {
		t.Fatalf("canonical invocation: err=%v stdout=%q stderr=%q", err, want, stderr.String())
	}
	for _, args := range [][]string{
		{"render", "-e", "text", "./-name"},
		{"render", "-e", "text", "--", "-name"},
		{"render", "./-name", "-e", "text"},
	} {
		t.Run("cli-05/"+strings.Join(args, "_"), func(t *testing.T) {
			cmd := binaryCommand(t, args...)
			cmd.Dir = dir
			binaryOutput(t, cmd, "", string(want), "", 0)
		})
	}
}

func TestBinaryInference(t *testing.T) {
	for _, ext := range []string{"txt", "svg", "unknown", ""} {
		t.Run("cli-23_cli-24/"+ext, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "output"+ext)
			if ext != "" {
				path = filepath.Join(filepath.Dir(path), "output."+ext)
			}
			cmd := binaryCommand(t, "render", "-o", path)
			if ext == "unknown" || ext == "" {
				binaryOutput(t, cmd, "flowchart LR\n A\n", "", "cannot infer the output format from "+path+"; pass -e\n", 2)
				return
			}
			binaryOutput(t, cmd, "flowchart LR\n A\n", "", "", 0)
			binaryFile(t, path, ext)
		})
	}
}

func binaryFile(t *testing.T, path, ext string) {
	t.Helper()
	content, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if ext == "txt" && string(content) != "\n ┌───┐\n │ A │\n └───┘\n\n" {
		t.Fatalf("text=%q", content)
	}
	if ext == "svg" && !bytes.Contains(content, []byte("<svg")) {
		t.Fatalf("SVG=%q", content)
	}
}

func TestBinaryWidth(t *testing.T) {
	t.Run("cli-25", func(t *testing.T) {
		binaryOutput(t, binaryCommand(t, "render", "-e", "text", "--color", "never", "--width", "1"), "flowchart LR\n A\n", "\n ┌───┐\n │ A │\n └───┘\n\n", "", 0)
	})
}

func TestBinaryColour(t *testing.T) {
	plain := "\n ┌───┐\n │ A │\n └───┘\n\n"
	coloured := "\n \x1b[90m┌───┐\x1b[39m\n \x1b[90m│ \x1b[39mA \x1b[90m│\x1b[39m\n \x1b[90m└───┘\x1b[39m\n\n"
	for _, tc := range []struct {
		name, flag string
		env        []string
		want       string
	}{
		{"always", "always", []string{"NO_COLOR=1"}, coloured},
		{"never", "never", []string{"FORCE_COLOR=1"}, plain},
		{"no_color", "auto", []string{"NO_COLOR=1", "FORCE_COLOR=1"}, plain},
		{"clicolor_force", "auto", []string{"CLICOLOR_FORCE=1", "CLICOLOR=0"}, coloured},
		{"force_color", "auto", []string{"FORCE_COLOR=1", "TERM=dumb"}, coloured},
		{"clicolor", "auto", []string{"CLICOLOR=0"}, plain},
		{"dumb", "auto", []string{"TERM=dumb"}, plain},
		{"pipe", "auto", nil, plain},
	} {
		t.Run("cli-36/"+tc.name, func(t *testing.T) {
			cmd := binaryCommand(t, "render", "-e", "text", "--color", tc.flag)
			cmd.Env = append(cmd.Env, tc.env...)
			binaryOutput(t, cmd, "flowchart LR\n A\n", tc.want, "", 0)
		})
	}
}

func TestBinaryColourTerminal(t *testing.T) {
	t.Run("cli-36/terminal", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(t.Context(), 20*time.Second)
		defer cancel()
		cmd := exec.CommandContext(ctx, "script", "-qec", "\"$EMD_BIN\" render -e text --color auto \"$SOURCE\"", "/dev/null")
		path := filepath.Join(t.TempDir(), "a.mmd")
		if err := os.WriteFile(path, []byte("flowchart LR\n A\n"), 0o600); err != nil {
			t.Fatal(err)
		}
		cmd.Env = []string{"PATH=" + os.Getenv("PATH"), "TERM=xterm", "EMD_BIN=" + binaryPath(t), "SOURCE=" + path}
		want := "\n \x1b[90m┌───┐\x1b[39m\n \x1b[90m│ \x1b[39mA \x1b[90m│\x1b[39m\n \x1b[90m└───┘\x1b[39m\n\n"
		binaryOutput(t, cmd, "", strings.ReplaceAll(want, "\n", "\r\n"), "", 0)
	})
}

func TestBinaryExplicitFormat(t *testing.T) {
	t.Run("cli-23", func(t *testing.T) {
		path := filepath.Join(t.TempDir(), "output.txt")
		binaryOutput(t, binaryCommand(t, "render", "-e", "svg", "-o", path), "flowchart LR\n A\n", "", "", 0)
		binaryFile(t, path, "svg")
	})
}
