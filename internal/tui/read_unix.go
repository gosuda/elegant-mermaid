//go:build aix || darwin || dragonfly || freebsd || linux || netbsd || openbsd || solaris

package tui

import (
	"errors"
	"io"
	"os"
	"time"

	"golang.org/x/sys/unix"
)

type unixInput struct{ fd int }

func newTerminalInput(file *os.File) (terminalInput, error) { return unixInput{int(file.Fd())}, nil }
func (unixInput) Close() error                              { return nil }
func (input unixInput) Read(delay time.Duration) ([]byte, error) {
	fds := []unix.PollFd{{Fd: int32(input.fd), Events: unix.POLLIN}}
	n, err := unix.Poll(fds, max(0, int((delay+time.Millisecond-1)/time.Millisecond)))
	if errors.Is(err, unix.EINTR) {
		return nil, nil
	}
	if err != nil || n == 0 {
		return nil, err
	}
	if fds[0].Revents&unix.POLLIN == 0 {
		return nil, io.EOF
	}
	buf := make([]byte, 4096)
	n, err = unix.Read(input.fd, buf)
	return buf[:max(0, n)], err
}
