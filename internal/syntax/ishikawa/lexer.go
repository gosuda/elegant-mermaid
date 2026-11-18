package ishikawa

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var headerWords = [...]string{"ishikawa-beta", "ishikawa"}

const (
	kindSpaceLine = "SPACELINE"
	kindIshikawa  = "ISHIKAWA"
	kindNL        = "NL"
	kindSpaceList = "SPACELIST"
	kindText      = "TEXT"
	kindEOF       = "EOF"
	kindEnd       = "END"
)

type scanner struct {
	text    string
	orig    []int
	end     int
	at      int
	eofSent bool
	crossed bool
	pending *Token
}

func newScanner(src string, removed []source.Span) *scanner {
	filtered, orig := filterRemoved(src, removed)
	start := 0
	for start < len(filtered) {
		r, n := unit(filtered, start)
		if !IsSpace(r) {
			break
		}
		start += n
	}
	return &scanner{text: filtered[start:] + "\n", orig: orig[start:], end: len(src)}
}

func filterRemoved(src string, removed []source.Span) (string, []int) {
	var text strings.Builder
	orig := make([]int, 0, len(src))
	at := 0
	for _, span := range removed {
		from, to := max(span.Start, at), min(span.End, len(src))
		if from >= to {
			continue
		}
		for i := at; i < from; i++ {
			orig = append(orig, i)
		}
		text.WriteString(src[at:from])
		at = to
	}
	for i := at; i < len(src); i++ {
		orig = append(orig, i)
	}
	text.WriteString(src[at:])
	return text.String(), orig
}

func unit(text string, at int) (rune, int) {
	c := text[at]
	switch {
	case c == '\r':
		if at+1 < len(text) && text[at+1] == '\n' {
			return '\n', 2
		}
		return '\n', 1
	case c < utf8.RuneSelf:
		return rune(c), 1
	}
	return utf8.DecodeRuneInString(text[at:])
}

func IsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func isNewline(r rune) bool { return r == '\n' }

func isDot(r rune) bool { return r != '\n' && r != 0x2028 && r != 0x2029 }

func isWordByte(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func (s *scanner) start(at int) int {
	if at >= len(s.orig) {
		return s.end
	}
	return s.orig[at]
}

func (s *scanner) finish(at int) int {
	if at <= 0 {
		return s.start(0)
	}
	if at > len(s.orig) {
		return s.end
	}
	return s.orig[at-1] + 1
}

func (s *scanner) span(from, to int) source.Span {
	return source.Span{Start: s.start(from), End: max(s.finish(to), s.start(from))}
}

func (s *scanner) token(kind string, from, to int) Token {
	s.at = to
	return Token{Kind: kind, Text: s.text[from:to], Span: s.span(from, to)}
}

func (s *scanner) run(at int, keep func(rune) bool) int {
	for at < len(s.text) {
		r, n := unit(s.text, at)
		if !keep(r) {
			break
		}
		at += n
	}
	return at
}

func (s *scanner) fold(at int, word string) bool {
	if at+len(word) > len(s.text) {
		return false
	}
	for i := range len(word) {
		c := s.text[at+i]
		if c >= 'A' && c <= 'Z' {
			c += 'a' - 'A'
		}
		if c != word[i] {
			return false
		}
	}
	return true
}

func (s *scanner) next() Token {
	if s.pending != nil {
		token := *s.pending
		s.pending = nil
		return token
	}
	return s.step()
}

func (s *scanner) step() Token {
	if s.at >= len(s.text) {
		zero := source.Span{Start: s.end, End: s.end}
		if s.eofSent {
			return Token{Kind: kindEnd, Span: zero}
		}
		s.eofSent = true
		return Token{Kind: kindEOF, Span: zero}
	}
	return s.initial()
}

func (s *scanner) commentEnd(at int) (int, bool) {
	j := s.run(at, IsSpace)
	if !strings.HasPrefix(s.text[j:], "%%") {
		return 0, false
	}
	return s.run(j+2, isDot), true
}

func (s *scanner) spaceLineEnd(at int) (int, bool) {
	last := -1
	for j := at; j < len(s.text); {
		r, n := unit(s.text, j)
		if !IsSpace(r) {
			break
		}
		if r == '\n' && j > at {
			last = j + n
		}
		j += n
	}
	return last, last >= 0
}

func (s *scanner) headerEnd(at int) (int, bool) {
	for _, word := range headerWords {
		end := at + len(word)
		if s.fold(at, word) && (end >= len(s.text) || !isWordByte(s.text[end])) {
			return end, true
		}
	}
	return 0, false
}

func (s *scanner) initial() Token {
	at := s.at
	if end, ok := s.commentEnd(at); ok {
		return s.token(kindSpaceLine, at, end)
	}
	if end, ok := s.headerEnd(at); ok {
		return s.token(kindIshikawa, at, end)
	}
	if end, ok := s.spaceLineEnd(at); ok {
		s.crossed = true
		return s.token(kindSpaceLine, at, end)
	}
	if end := s.run(at, isNewline); end > at {
		s.crossed = true
		return s.token(kindNL, at, end)
	}
	if end := s.run(at, IsSpace); end > at {
		return s.token(kindSpaceList, at, end)
	}
	return s.token(kindText, at, s.run(at, func(r rune) bool { return r != '\n' }))
}

func isSeparator(kind string) bool {
	switch kind {
	case kindNL, kindSpaceLine, kindEOF, kindEnd:
		return true
	}
	return false
}

func (s *scanner) skipLine(contentEnd int) int {
	for {
		s.crossed = false
		token := s.step()
		switch token.Kind {
		case kindEOF, kindEnd:
			s.pending = &token
			return contentEnd
		}
		if !isSeparator(token.Kind) {
			contentEnd = max(contentEnd, token.Span.End)
		}
		if s.crossed {
			return contentEnd
		}
	}
}
