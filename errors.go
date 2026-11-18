package mermaid

import "errors"

var (
	ErrInvalidDocument = errors.New("invalid document")
	ErrTooLarge        = errors.New("model exceeds a limit")
	ErrOverflow        = errors.New("arithmetic overflow")
	ErrBadConfig       = errors.New("invalid option or config")
	ErrBadIconPack     = errors.New("malformed icon pack")
)
