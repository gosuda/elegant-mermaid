package tui

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
)

func stripSGR(text string) string {
	var out strings.Builder
	for len(text) > 0 {
		if n := sgrLength(text); n > 0 {
			text = text[n:]
			continue
		}
		r, n := utf8.DecodeRuneInString(text)
		out.WriteRune(r)
		text = text[n:]
	}
	return out.String()
}

func sgrLength(text string) int {
	if !strings.HasPrefix(text, "\x1b[") {
		return 0
	}
	for i := 2; i < len(text); i++ {
		if text[i] == 'm' {
			return i + 1
		}
		if text[i] != ';' && (text[i] < '0' || text[i] > '9') {
			break
		}
	}
	return 0
}

func coloredSlice(text string, offset, width int) string {
	var out strings.Builder
	position := 0
	current := "\x1b[39m"
	started := false
	for len(text) > 0 && position < offset+width {
		if n := sgrLength(text); n > 0 {
			current = text[:n]
			if started {
				out.WriteString(current)
			}
			text = text[n:]
			continue
		}
		r, n := utf8.DecodeRuneInString(text)
		text = text[n:]
		if position >= offset {
			writeColoredRune(&out, r, current, &started)
		}
		position++
	}
	out.WriteString("\x1b[39m")
	out.WriteString(strings.Repeat(" ", max(0, width-max(0, position-offset))))
	return out.String()
}

func writeColoredRune(out *strings.Builder, r rune, current string, started *bool) {
	if !*started {
		out.WriteString(current)
		*started = true
	}
	if r < 32 || r == 127 {
		r = '�'
	}
	out.WriteRune(r)
}

func terminalText(s State) string {
	rows := strings.Split(strings.TrimSuffix(Frame(s), "\n"), "\n")
	if s.Color == 0 || s.Mode != termgfx.ModeCells || s.Panel != "" || s.Empty || s.MissingBlocks || s.FrameRev == 0 {
		return strings.Join(rows, "\r\n")
	}
	for r := range s.Height - 2 {
		index := s.OffsetY + r
		if index < len(s.ColoredText) {
			rows[r] = coloredSlice(s.ColoredText[index], s.OffsetX, s.Width)
		}
	}
	return strings.Join(rows, "\r\n")
}
