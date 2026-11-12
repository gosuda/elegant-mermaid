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

func TestLayoutModel(t *testing.T) {
	path := filepath.Join(t.TempDir(), "demo.mmd")
	if err := os.WriteFile(path, []byte("flowchart\nA --> B\n"), 0600); err != nil {
		t.Fatal(err)
	}
	cases := []struct {
		name   string
		args   []string
		source string
		code   int
	}{
		{"file", []string{"layout", "--stage", "model", path}, "", 0},
		{"stdin", []string{"layout", "-", "--stage", "model", "--profile", "cell"}, "flowchart\nA --> B\n", 0},
		{"parse", []string{"layout", "--stage", "model", "-"}, "flowchart\nA[broken\n", 1},
		{"stage", []string{"layout", "--stage", "bad", "-"}, "", 2},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			var out, stderr bytes.Buffer
			err := Run(context.Background(), Config{Args: c.args, Stdin: strings.NewReader(c.source), Stdout: &out, Stderr: &stderr})
			code := layoutExitCode(t, err)
			if code != c.code {
				t.Fatalf("code %d: %s", code, stderr.String())
			}
			if code == 0 && !strings.Contains(out.String(), `"stage":"model"`) {
				t.Fatal(out.String())
			}
			if code == 1 && (out.Len() != 0 || !strings.Contains(stderr.String(), "error[")) {
				t.Fatal("bad diagnostic streams")
			}
		})
	}
}

func layoutExitCode(t *testing.T, err error) int {
	t.Helper()
	if exit, ok := errors.AsType[*ExitError](err); ok {
		return exit.Code
	}
	if err != nil {
		t.Fatal(err)
	}
	return 0
}

func TestLayoutPublic(t *testing.T) {
	for _, profile := range []string{"vector", "cell"} {
		var out, stderr bytes.Buffer
		err := Run(context.Background(), Config{Args: []string{"layout", "--profile", profile}, Stdin: strings.NewReader("flowchart LR\n A[Start] --> B{Choice}\n B -->|yes| C[Done]\n B -->|no| A\n"), Stdout: &out, Stderr: &stderr})
		if layoutExitCode(t, err) != 0 || !strings.Contains(out.String(), `"stage":"layout"`) {
			t.Fatalf("%v %s %s", err, out.String(), stderr.String())
		}
	}
}

func TestMetricsCellRefusal(t *testing.T) {
	var out, stderr bytes.Buffer
	err := Run(t.Context(), Config{Args: []string{"layout", "--metrics", "--profile", "cell"}, Stdin: strings.NewReader("flowchart\nA\n"), Stdout: &out, Stderr: &stderr})
	if layoutExitCode(t, err) != 2 || stderr.String() != "--metrics needs --profile vector\n" || out.Len() != 0 {
		t.Fatalf("%v stdout=%q stderr=%q", err, out.String(), stderr.String())
	}
}
