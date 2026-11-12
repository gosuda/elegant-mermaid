package cli

import (
	"bytes"
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
)

func TestKernelEvalBinary(t *testing.T) {
	binary := filepath.Join(t.TempDir(), "emd")
	build := exec.CommandContext(t.Context(), "go", "build", "-o", binary, "../../cmd/emd")
	if output, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build: %v: %s", err, output)
	}
	cases := filepath.Join(t.TempDir(), "cases.txt")
	if err := os.WriteFile(cases, []byte("isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\nbroken\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	cmd := exec.CommandContext(t.Context(), binary, "kernel-eval", cases)
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	err := cmd.Run()
	exit, ok := errors.AsType[*exec.ExitError](err)
	if !ok || exit.ExitCode() != 2 {
		t.Fatalf("exit: %v", err)
	}
	if stdout.String() != "9\n2\n" || stderr.String() != "bad case line 3\n" {
		t.Fatalf("stdout=%q stderr=%q", &stdout, &stderr)
	}
}

func TestUnsupportedInvocations(t *testing.T) {
	for _, args := range [][]string{nil, {"render"}, {"--version"}, {"--help"}, {"kernel-eval", "--help"}, {"kernel-eval", "a", "b"}} {
		var stdout, stderr bytes.Buffer
		err := Run(t.Context(), Config{Args: args, Stdout: &stdout, Stderr: &stderr})
		exit, ok := errors.AsType[*ExitError](err)
		if !ok || exit.Code != 2 || stdout.Len() != 0 || stderr.String() != usage {
			t.Fatalf("%q: %v stdout=%q stderr=%q", args, err, &stdout, &stderr)
		}
	}
}
