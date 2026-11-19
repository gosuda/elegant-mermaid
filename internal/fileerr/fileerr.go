package fileerr

import (
	"errors"
	"io/fs"
	"syscall"
)

const (
	readVerb  = "read"
	writeVerb = "write"
)

type Error struct {
	Verb string
	Path string
	Err  error
}

func (e *Error) Error() string { return "cannot " + e.Verb + " " + e.Path + ": " + Text(e.Err) }

func (e *Error) Unwrap() error { return e.Err }

func Read(path string, err error) error { return &Error{Verb: readVerb, Path: path, Err: err} }

func Write(path string, err error) error { return &Error{Verb: writeVerb, Path: path, Err: err} }

func Text(err error) string {
	if errno, ok := errors.AsType[syscall.Errno](err); ok {
		return errno.Error()
	}
	if pathError, ok := errors.AsType[*fs.PathError](err); ok {
		return pathError.Err.Error()
	}
	return err.Error()
}
