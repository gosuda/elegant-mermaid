package termgfx

import (
	"errors"
	"fmt"
)

const (
	escByte byte = 0x1b
	belByte byte = 0x07
	stSeq        = "\x1b\\"

	FallbackCellW = 8
	FallbackCellH = 16
)

var (
	ErrBuffer = errors.New("termgfx: buffer shorter than its width and height")
	ErrSize   = errors.New("termgfx: negative image size")
	ErrMode   = errors.New("termgfx: unknown graphics mode")
)

type Mode uint8

const (
	ModeCells Mode = iota
	ModeKitty
	ModeITerm2
	ModeSixel
)

func (m Mode) String() string {
	switch m {
	case ModeKitty:
		return "kitty"
	case ModeITerm2:
		return "iterm"
	case ModeSixel:
		return "sixel"
	case ModeCells:
		return "cells"
	}
	return "unknown"
}

func (m Mode) Pixel() bool {
	return m != ModeCells
}

func ParseMode(name string) (Mode, error) {
	switch name {
	case "cells":
		return ModeCells, nil
	case "kitty":
		return ModeKitty, nil
	case "iterm":
		return ModeITerm2, nil
	case "sixel":
		return ModeSixel, nil
	}
	return ModeCells, fmt.Errorf("%w: %q", ErrMode, name)
}

type Env struct {
	KittyWindowID string
	Term          string
	TermProgram   string
}

func (e Env) KittyCandidate() bool {
	if e.KittyWindowID != "" || e.Term == "xterm-kitty" {
		return true
	}
	return e.TermProgram == "ghostty" || e.TermProgram == "WezTerm"
}

type Replies struct {
	KittyOK bool
	CellW   int
	CellH   int
	Sixel   bool
}
