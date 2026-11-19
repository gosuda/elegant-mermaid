package cli

import (
	"bytes"
	"errors"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestKernelEvalInputs(t *testing.T) {
	for _, bad := range []bool{false, true} {
		source := "isqrt 99 -> 9\ncount_inversions [3,1,2] -> 2\n"
		if bad {
			source += "broken\n"
		}
		path := filepath.Join(t.TempDir(), "cases")
		if err := os.WriteFile(path, []byte(source), 0o600); err != nil {
			t.Fatal(err)
		}
		for _, operands := range [][]string{nil, {"-"}, {path}} {
			checkKernelInput(t, operands, source, bad)
		}
	}
}

func checkKernelInput(t *testing.T, operands []string, source string, bad bool) {
	t.Helper()
	var out, stderr bytes.Buffer
	err := Run(t.Context(), Config{Args: append([]string{"kernel-eval"}, operands...), Stdin: strings.NewReader(source), Stdout: &out, Stderr: &stderr})
	if out.String() != "9\n2\n" {
		t.Fatalf("%v: output %q", operands, out.String())
	}
	if !bad {
		if err != nil || stderr.Len() != 0 {
			t.Fatalf("%v: %v, %q", operands, err, stderr.String())
		}
		return
	}
	exit, ok := errors.AsType[*ExitError](err)
	if !ok || exit.Code != 2 || stderr.String() != "bad case line 3\n" {
		t.Fatalf("%v: %v, %q", operands, err, stderr.String())
	}
}
