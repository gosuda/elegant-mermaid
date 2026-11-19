package sankey

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type lexMode uint8

const (
	modeInitial lexMode = iota
	modeCsv
	modeEscaped
)

const (
	headerBeta  = "sankey-beta"
	headerPlain = "sankey"
)

type cell struct {
	r    rune
	span source.Span
}

type scanner struct {
	cells  []cell
	at     int
	end    int
	opener int
	modes  []lexMode
	tokens []Token
}

func lex(src string, removed []source.Span) []Token {
	s := &scanner{cells: prepare(src, removed), end: len(src), modes: []lexMode{modeInitial}}
	return s.run()
}

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func prepare(src string, removed []source.Span) []cell {
	var out []cell
	next := 0
	for at := 0; at < len(src); {
		for next < len(removed) && removed[next].End <= at {
			next++
		}
		r, size := utf8.DecodeRuneInString(src[at:])
		if next < len(removed) && removed[next].Start <= at {
			at = max(removed[next].End, at+1)
			continue
		}
		span := source.Span{Start: at, End: at + size}
		at += size
		if r != '\n' && r != '\r' {
			out = append(out, cell{r: r, span: span})
			continue
		}
		if n := len(out); n > 0 && out[n-1].r == '\n' {
			out[n-1].span.End = span.End
			continue
		}
		out = append(out, cell{r: '\n', span: span})
	}
	return trim(out)
}

func trim(cells []cell) []cell {
	lo, hi := 0, len(cells)
	for lo < hi && jsSpace(cells[lo].r) {
		lo++
	}
	for hi > lo && jsSpace(cells[hi-1].r) {
		hi--
	}
	return cells[lo:hi]
}

func isTextData(r rune) bool {
	return r >= 0x20 && r <= 0x21 || r >= 0x23 && r <= 0x2b || r >= 0x2d && r <= 0x7e
}

func (s *scanner) mode() lexMode { return s.modes[len(s.modes)-1] }

func (s *scanner) pop() { s.modes = s.modes[:len(s.modes)-1] }

func (s *scanner) push(m lexMode) { s.modes = append(s.modes, m) }

func (s *scanner) spanOf(from, to int) source.Span {
	return source.Span{Start: s.cells[from].span.Start, End: s.cells[to-1].span.End}
}

func (s *scanner) text(from, to int) string {
	var b strings.Builder
	for _, c := range s.cells[from:to] {
		b.WriteRune(c.r)
	}
	return b.String()
}

func (s *scanner) emit(kind string, length int) {
	s.tokens = append(s.tokens, Token{Kind: kind, Text: s.text(s.at, s.at+length), Span: s.spanOf(s.at, s.at+length)})
	s.at += length
}

func (s *scanner) run() []Token {
	for s.at < len(s.cells) {
		if s.mode() == modeEscaped {
			s.lexEscaped()
		} else {
			s.lexPlain()
		}
	}
	if s.mode() == modeEscaped {
		span := source.Span{Start: s.cells[s.opener].span.Start, End: s.end}
		return append(s.tokens, Token{Kind: "UNTERMINATED", Text: "\"", Span: span})
	}
	return append(s.tokens, Token{Kind: "EOF", Span: source.Span{Start: s.end, End: s.end}})
}

func (s *scanner) matches(word string) bool {
	if s.at+len(word) > len(s.cells) {
		return false
	}
	for i, w := range []byte(word) {
		if s.cells[s.at+i].r != rune(w) {
			return false
		}
	}
	return true
}

func (s *scanner) lexHeader() bool {
	for _, word := range []string{headerBeta, headerPlain} {
		if s.matches(word) {
			s.emit("SANKEY", len(word))
			s.push(modeCsv)
			return true
		}
	}
	return false
}

func (s *scanner) lexPlain() {
	if s.mode() == modeInitial && s.lexHeader() {
		return
	}
	switch c := s.cells[s.at].r; {
	case c == '\n':
		s.emit("NEWLINE", 1)
	case c == ',':
		s.emit("COMMA", 1)
	case c == '"':
		s.opener = s.at
		s.emit("DQUOTE", 1)
		s.push(modeEscaped)
	case isTextData(c):
		s.emit("NON_ESCAPED_TEXT", s.textRun())
	default:
		s.emit("INVALID", 1)
	}
}

func (s *scanner) textRun() int {
	n := 0
	for s.at+n < len(s.cells) && isTextData(s.cells[s.at+n].r) {
		n++
	}
	return n
}

func (s *scanner) quoteAt(i int) bool { return i < len(s.cells) && s.cells[i].r == '"' }

func (s *scanner) lexEscaped() {
	if s.quoteAt(s.at) && !s.quoteAt(s.at+1) {
		s.emit("DQUOTE", 1)
		s.pop()
		return
	}
	if n := s.escapedRun(); n > 0 {
		s.emit("ESCAPED_TEXT", n)
		return
	}
	s.emit("INVALID", 1)
}

func (s *scanner) escapedRun() int {
	n := 0
	for at := s.at; at < len(s.cells); {
		switch c := s.cells[at].r; {
		case isTextData(c) || c == ',' || c == '\n':
			at++
		case c == '"' && s.quoteAt(at+1):
			at += 2
		default:
			return at - s.at
		}
		n = at - s.at
	}
	return n
}
