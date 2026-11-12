package diag

import (
	"io"
	"strconv"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type FrameOptions struct {
	Width func(r rune) int
}

type frameStyle struct {
	word func(dst []byte, s Severity) []byte
	mark func(dst []byte, s Severity, cells int) []byte
}

var plainStyle = frameStyle{word: appendWord, mark: appendMarkCells}

var colourStyle = frameStyle{word: appendWordColour, mark: appendMarkColour}

func RenderText(w io.Writer, path string, src []byte, ds []Diagnostic, o FrameOptions) error {
	return writeFrames(w, plainStyle, path, src, ds, o)
}

func RenderTextColour(w io.Writer, path string, src []byte, ds []Diagnostic, o FrameOptions) error {
	return writeFrames(w, colourStyle, path, src, ds, o)
}

type frameWriter struct {
	style frameStyle
	path  string
	src   []byte
	index *source.Index
	width func(rune) int
}

func writeFrames(w io.Writer, st frameStyle, path string, src []byte, ds []Diagnostic, o FrameOptions) error {
	fw := frameWriter{style: st, path: path, src: src, index: source.NewIndex(src), width: o.Width}
	if fw.width == nil {
		fw.width = unitWidth
	}
	out := make([]byte, 0, 192*len(ds))
	for i := range ds {
		if i > 0 {
			out = append(out, '\n')
		}
		out = fw.frame(out, &ds[i])
	}
	_, err := w.Write(out)
	return err
}

func (fw *frameWriter) frame(dst []byte, d *Diagnostic) []byte {
	pos := fw.index.Position(d.Span.Start)
	line := fw.index.LineContent(pos.Line)
	from, to := clampSpan(d.Span, line)
	at := columnAt(fw.src, line, from, fw.width)
	cells := cellsOf(at, columnAt(fw.src, line, to, fw.width))
	dst = fw.header(dst, pos, d)
	dst = appendBar(dst, pos.Line)
	dst = appendSource(dst, pos.Line, lineText(fw.src, line, fw.width))
	dst = fw.underline(dst, pos.Line, at, cells, d.Severity)
	return fw.notes(dst, d)
}

func (fw *frameWriter) header(dst []byte, pos source.Position, d *Diagnostic) []byte {
	dst = append(dst, fw.path...)
	dst = append(dst, ':')
	dst = strconv.AppendInt(dst, int64(pos.Line), 10)
	dst = append(dst, ':')
	dst = strconv.AppendInt(dst, int64(pos.Column), 10)
	dst = append(dst, ':', ' ')
	dst = fw.style.word(dst, d.Severity)
	dst = append(dst, '[')
	dst = append(dst, d.Code...)
	dst = append(dst, ']', ':', ' ')
	dst = append(dst, d.Message...)
	return append(dst, '\n')
}

func (fw *frameWriter) underline(dst []byte, line, at, cells int, s Severity) []byte {
	dst = appendGutter(dst, line, " | ")
	dst = appendSpaces(dst, at)
	dst = fw.style.mark(dst, s, cells)
	return append(dst, '\n')
}

func (fw *frameWriter) notes(dst []byte, d *Diagnostic) []byte {
	dst = appendLine(dst, "  = help: ", d.Help)
	for i := range d.Fixes {
		dst = appendLine(dst, "  = fix: ", d.Fixes[i].Title)
	}
	for i := range d.Related {
		dst = fw.note(dst, &d.Related[i])
	}
	return dst
}

func (fw *frameWriter) note(dst []byte, rel *Related) []byte {
	pos := fw.index.Position(rel.Span.Start)
	dst = append(dst, "  = note: "...)
	dst = append(dst, rel.Message...)
	dst = append(dst, " at "...)
	dst = append(dst, fw.path...)
	dst = append(dst, ':')
	dst = strconv.AppendInt(dst, int64(pos.Line), 10)
	dst = append(dst, ':')
	dst = strconv.AppendInt(dst, int64(pos.Column), 10)
	return append(dst, '\n')
}

func appendLine(dst []byte, prefix, body string) []byte {
	if body == "" {
		return dst
	}
	dst = append(dst, prefix...)
	dst = append(dst, body...)
	return append(dst, '\n')
}

func appendWord(dst []byte, s Severity) []byte {
	return append(dst, s.String()...)
}

func appendWordColour(dst []byte, s Severity) []byte {
	dst = appendSGR(dst, sgrOf(s))
	dst = append(dst, s.String()...)
	return appendReset(dst)
}

func appendMarkCells(dst []byte, _ Severity, cells int) []byte {
	dst = append(dst, '^')
	return appendRepeats(dst, '~', cells-1)
}

func appendMarkColour(dst []byte, s Severity, cells int) []byte {
	dst = appendSGR(dst, sgrOf(s))
	dst = appendMarkCells(dst, s, cells)
	return appendReset(dst)
}

func appendSGR(dst []byte, code int) []byte {
	dst = append(dst, "\x1b["...)
	dst = strconv.AppendInt(dst, int64(code), 10)
	return append(dst, 'm')
}

func appendReset(dst []byte) []byte {
	return append(dst, "\x1b[0m"...)
}

func appendBar(dst []byte, line int) []byte {
	dst = appendGutter(dst, line, " |")
	return append(dst, '\n')
}

func appendGutter(dst []byte, line int, tail string) []byte {
	dst = appendSpaces(dst, gutterWidth(line))
	return append(dst, tail...)
}

func appendSource(dst []byte, line int, text []byte) []byte {
	dst = strconv.AppendInt(dst, int64(line), 10)
	dst = append(dst, " | "...)
	dst = append(dst, text...)
	return append(dst, '\n')
}

func clampSpan(sp, line source.Span) (int, int) {
	from := clampInt(sp.Start, line.Start, line.End)
	return from, clampInt(sp.End, from, line.End)
}

func cellsOf(at, end int) int {
	if end <= at {
		return 1
	}
	return end - at
}

func clampInt(v, low, high int) int {
	if v < low {
		return low
	}
	if v > high {
		return high
	}
	return v
}

func gutterWidth(line int) int {
	return len(strconv.Itoa(line))
}

func lineText(src []byte, line source.Span, width func(rune) int) []byte {
	out := make([]byte, 0, line.End-line.Start)
	col := 0
	for at := line.Start; at < line.End; {
		r, size, next := stepCell(src, at, col, width)
		if r == '\t' {
			out = appendSpaces(out, next-col)
		} else {
			out = utf8.AppendRune(out, r)
		}
		col = next
		at += size
	}
	return out
}

func columnAt(src []byte, line source.Span, offset int, width func(rune) int) int {
	col := 0
	for at := line.Start; at < offset; {
		_, size, next := stepCell(src, at, col, width)
		col = next
		at += size
	}
	return col
}

func stepCell(src []byte, at, col int, width func(rune) int) (rune, int, int) {
	if src[at] == '\t' {
		return '\t', 1, col + 8 - col%8
	}
	r, size := utf8.DecodeRune(src[at:])
	r = printable(r)
	return r, size, col + cellAdvance(r, width)
}

func printable(r rune) rune {
	if r < 0x20 || (r >= 0x7F && r <= 0x9F) {
		return utf8.RuneError
	}
	return r
}

func cellAdvance(r rune, width func(rune) int) int {
	n := width(r)
	if n < 0 {
		return 0
	}
	return n
}

func appendSpaces(dst []byte, n int) []byte {
	return appendRepeats(dst, ' ', n)
}

func appendRepeats(dst []byte, b byte, n int) []byte {
	for range n {
		dst = append(dst, b)
	}
	return dst
}

func unitWidth(rune) int {
	return 1
}

func sgrOf(s Severity) int {
	switch s {
	case SeverityError:
		return 31
	case SeverityWarning:
		return 33
	}
	return 36
}
