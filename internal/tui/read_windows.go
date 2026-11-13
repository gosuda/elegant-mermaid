package tui

import (
	"os"
	"strings"
	"time"

	console "github.com/charmbracelet/x/windows"
	"golang.org/x/sys/windows"
)

type windowsInput struct{ handle windows.Handle }

func newTerminalInput(file *os.File) (terminalInput, error) {
	handle := windows.Handle(file.Fd())
	var mode uint32
	if err := windows.GetConsoleMode(handle, &mode); err != nil {
		return nil, err
	}
	return windowsInput{handle: handle}, nil
}

func (windowsInput) Close() error { return nil }

func (input windowsInput) Read(delay time.Duration) ([]byte, error) {
	deadline := time.Now().Add(delay)
	for time.Now().Before(deadline) {
		wait := max(0, int((time.Until(deadline)+time.Millisecond-1)/time.Millisecond))
		event, err := windows.WaitForSingleObject(input.handle, uint32(wait))
		if err != nil {
			return nil, err
		}
		if event == windows.WAIT_TIMEOUT {
			return nil, nil
		}
		var record console.InputRecord
		var count uint32
		if err = console.PeekConsoleInput(input.handle, &record, 1, &count); err != nil {
			return nil, err
		}
		if count == 0 {
			continue
		}
		if err = console.ReadConsoleInput(input.handle, &record, 1, &count); err != nil {
			return nil, err
		}
		if count == 0 || record.EventType != 1 {
			continue
		}
		key := record.KeyEvent()
		if !key.KeyDown {
			continue
		}
		text := consoleKey(key)
		return []byte(strings.Repeat(text, int(key.RepeatCount))), nil
	}
	return nil, nil
}

func consoleKey(key console.KeyEventRecord) string {
	if key.Char != 0 {
		return string(key.Char)
	}
	switch key.VirtualKeyCode {
	case 0x25:
		return "\x1b[D"
	case 0x26:
		return "\x1b[A"
	case 0x27:
		return "\x1b[C"
	case 0x28:
		return "\x1b[B"
	}
	return ""
}
