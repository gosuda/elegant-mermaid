//go:build !aix && !darwin && !dragonfly && !freebsd && !linux && !netbsd && !openbsd && !solaris && !windows

package tui

import (
	"errors"
	"os"
	"time"
)

type deadlineInput struct{ file *os.File }

func newTerminalInput(file *os.File) (terminalInput, error) {
	if err := file.SetReadDeadline(time.Time{}); err != nil {
		return nil, err
	}
	return deadlineInput{file: file}, nil
}

func (input deadlineInput) Read(delay time.Duration) ([]byte, error) {
	if err := input.file.SetReadDeadline(time.Now().Add(delay)); err != nil {
		return nil, err
	}
	buffer := make([]byte, 4096)
	n, err := input.file.Read(buffer)
	if errors.Is(err, os.ErrDeadlineExceeded) {
		return buffer[:n], nil
	}
	return buffer[:n], err
}

func (input deadlineInput) Close() error { return input.file.SetReadDeadline(time.Time{}) }
