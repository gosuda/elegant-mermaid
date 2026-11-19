package fileerr

import (
	"errors"
	"io/fs"
	"os"
	"path/filepath"
	"syscall"
	"testing"
)

func TestReadAndWriteWordTheOSErrorText(t *testing.T) {
	missing := filepath.Join(t.TempDir(), "missing")
	_, err := os.ReadFile(missing)
	if got, want := Read(missing, err).Error(), "cannot read "+missing+": no such file or directory"; got != want {
		t.Fatalf("Read = %q, want %q", got, want)
	}
	if got, want := Write("out.svg", err).Error(), "cannot write out.svg: no such file or directory"; got != want {
		t.Fatalf("Write = %q, want %q", got, want)
	}
}

func TestTextDropsOperationAndPath(t *testing.T) {
	dir := t.TempDir()
	_, readDir := os.ReadFile(dir)
	renamed := os.Rename(filepath.Join(dir, "absent"), filepath.Join(dir, "target"))
	cases := []struct {
		name string
		err  error
		want string
	}{
		{"directory", readDir, "is a directory"},
		{"rename", renamed, "no such file or directory"},
		{"bare errno", syscall.EACCES, "permission denied"},
		{"path error with a plain cause", &fs.PathError{Op: "open", Path: "x", Err: fs.ErrPermission}, "permission denied"},
		{"no operating system cause", errors.New("closed"), "closed"},
	}
	for _, c := range cases {
		if got := Text(c.err); got != c.want {
			t.Errorf("%s: Text = %q, want %q", c.name, got, c.want)
		}
	}
}

func TestErrorKeepsItsCause(t *testing.T) {
	_, err := os.ReadFile(filepath.Join(t.TempDir(), "missing"))
	wrapped := Read("missing", err)
	if !errors.Is(wrapped, fs.ErrNotExist) {
		t.Fatalf("errors.Is(%v, fs.ErrNotExist) = false", wrapped)
	}
	if _, ok := errors.AsType[*Error](wrapped); !ok {
		t.Fatalf("errors.AsType[*Error](%v) = false", wrapped)
	}
}
