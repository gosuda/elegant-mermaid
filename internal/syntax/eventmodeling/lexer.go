package eventmodeling

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	kindID       = "EM_ID"
	kindFID      = "EM_FID"
	kindInline   = "EM_DATA_INLINE"
	kindBlock    = "EM_DATA_BLOCK"
	kindInvalid  = "INVALID"
	kindUnclosed = "UNTERMINATED"
	kindEOF      = "EOF"
	headerKind   = "eventmodeling"
	maxFrameID   = 3
)

var keywords = map[string]struct{}{
	headerKind: {}, "rmo": {}, "readmodel": {}, "ui": {}, "cmd": {}, "command": {}, "evt": {}, "event": {},
	"pcr": {}, "processor": {}, "json": {}, "jsobj": {}, "figma": {}, "salt": {}, "uri": {}, "md": {},
	"html": {}, "text": {}, "tf": {}, "timeframe": {}, "rf": {}, "resetframe": {}, "entity": {},
	"data": {}, "note": {}, "gwt": {}, "given": {}, "when": {}, "then": {},
}

func lex(src string, removed []source.Span) ([]Token, []int) {
	s := &scanner{src: src, removed: removed}
	s.run()
	return s.tokens, s.breaks
}

type scanner struct {
	src     string
	removed []source.Span
	at      int
	tokens  []Token
	breaks  []int
}

func (s *scanner) run() {
	for s.at < len(s.src) {
		if end, ok := s.removedEnd(); ok {
			s.at = end
			continue
		}
		if !s.next() {
			s.emitRune(kindInvalid)
		}
	}
	end := len(s.src)
	s.tokens = append(s.tokens, Token{Kind: kindEOF, Span: source.Span{Start: end, End: end}})
}

func (s *scanner) removedEnd() (int, bool) {
	for _, span := range s.removed {
		if span.Start <= s.at && s.at < span.End {
			return span.End, true
		}
	}
	return 0, false
}

func (s *scanner) next() bool {
	c := s.src[s.at]
	switch {
	case s.whitespace():
		return true
	case c == '/':
		return s.slash()
	case c == '%':
		return s.percent()
	case c == '-':
		return s.dash()
	case c == '[' || c == ']':
		return s.bracket(c)
	}
	return s.atom(c)
}

func (s *scanner) atom(c byte) bool {
	switch {
	case isWordStart(c):
		s.word()
	case isDigit(c):
		s.frameID()
	case c == '{':
		s.brace()
	case c == '"' || c == '\'':
		s.quoted(c)
	case c == '`' || c == '.':
		s.emit(string(c), 1)
	default:
		return false
	}
	return true
}

func (s *scanner) emit(kind string, length int) {
	end := s.at + length
	s.tokens = append(s.tokens, Token{Kind: kind, Text: s.src[s.at:end], Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) emitRune(kind string) {
	_, size := utf8.DecodeRuneInString(s.src[s.at:])
	s.emit(kind, size)
}

func (s *scanner) unterminated(opener, length int) {
	end := len(s.src)
	s.tokens = append(s.tokens, Token{Kind: kindUnclosed, Text: s.src[opener : opener+length], Span: source.Span{Start: opener, End: end}})
	s.at = end
}

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func (s *scanner) whitespace() bool {
	start := s.at
	for s.at < len(s.src) {
		r, size := utf8.DecodeRuneInString(s.src[s.at:])
		if !jsSpace(r) {
			break
		}
		switch r {
		case '\n':
			s.breaks = append(s.breaks, s.at)
		case '\r':
			s.breaks = append(s.breaks, s.at)
			if s.at+1 < len(s.src) && s.src[s.at+1] == '\n' {
				size++
			}
		}
		s.at += size
	}
	return s.at > start
}

func lineLength(text string) int {
	if i := strings.IndexAny(text, "\n\r"); i >= 0 {
		return i
	}
	return len(text)
}

func (s *scanner) slash() bool {
	rest := s.src[s.at:]
	switch {
	case strings.HasPrefix(rest, "//"):
		s.at += lineLength(rest)
	case strings.HasPrefix(rest, "/*"):
		closing := strings.Index(rest[2:], "*/")
		if closing < 0 {
			s.unterminated(s.at, 2)
			return true
		}
		s.at += 2 + closing + 2
	default:
		return false
	}
	return true
}

func (s *scanner) percent() bool {
	rest := s.src[s.at:]
	if !strings.HasPrefix(rest, "%%") {
		return false
	}
	s.at += lineLength(rest)
	return true
}

func isWordStart(c byte) bool {
	return c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
}

func isDigit(c byte) bool {
	return c >= '0' && c <= '9'
}

func isWord(c byte) bool {
	return isWordStart(c) || isDigit(c)
}

func (s *scanner) word() {
	rest := s.src[s.at:]
	n := 1
	for n < len(rest) && isWord(rest[n]) {
		n++
	}
	kind := kindID
	if _, reserved := keywords[rest[:n]]; reserved && (rest[:n] != headerKind || headerBoundary(rest[n:])) {
		kind = rest[:n]
	}
	s.emit(kind, n)
}

func headerBoundary(after string) bool {
	if after == "" || strings.HasPrefix(after, "%%") {
		return true
	}
	r, _ := utf8.DecodeRuneInString(after)
	return jsSpace(r)
}

func (s *scanner) frameID() {
	rest := s.src[s.at:]
	n := 1
	for n < len(rest) && n < maxFrameID && isDigit(rest[n]) {
		n++
	}
	s.emit(kindFID, n)
}

func (s *scanner) brace() {
	rest := s.src[s.at:]
	if end, ok := inlineEnd(rest, '}'); ok {
		s.emit(kindInline, end)
		return
	}
	if end, ok := blockEnd(rest, "{", "}"); ok {
		s.emit(kindBlock, end)
		return
	}
	s.unterminated(s.at, 1)
}

func (s *scanner) quoted(quote byte) {
	if end, ok := inlineEnd(s.src[s.at:], quote); ok {
		s.emit(kindInline, end)
		return
	}
	s.unterminated(s.at, 1)
}

func inlineEnd(rest string, closing byte) (int, bool) {
	line := len(rest)
	if i := strings.IndexAny(rest[1:], "\n\r\u2028\u2029"); i >= 0 {
		line = 1 + i
	}
	if i := strings.LastIndexByte(rest[1:line], closing); i >= 0 {
		return 1 + i + 1, true
	}
	return 0, false
}

func newlineLength(text string, at int) int {
	switch {
	case strings.HasPrefix(text[at:], "\r\n"):
		return 2
	case at < len(text) && (text[at] == '\n' || text[at] == '\r'):
		return 1
	}
	return 0
}

func blockEnd(rest, open, closing string) (int, bool) {
	if !strings.HasPrefix(rest, open) {
		return 0, false
	}
	first, ok := blockBody(rest, len(open))
	if !ok {
		return 0, false
	}
	if end, ok := closingLine(rest, first, closing); ok {
		return end, true
	}
	if strings.HasPrefix(rest[first:], closing) {
		return blockTail(rest, first+len(closing))
	}
	return 0, false
}

func blockBody(rest string, at int) (int, bool) {
	for at < len(rest) && (rest[at] == ' ' || rest[at] == '\t') {
		at++
	}
	n := newlineLength(rest, at)
	return at + n, n > 0
}

func closingLine(rest string, first int, closing string) (int, bool) {
	for k := first + 1; k < len(rest); k++ {
		if rest[k-1] != '\n' && rest[k-1] != '\r' || !strings.HasPrefix(rest[k:], closing) {
			continue
		}
		if end, ok := blockTail(rest, k+len(closing)); ok {
			return end, true
		}
	}
	return 0, false
}

func blockTail(rest string, at int) (int, bool) {
	if at >= len(rest) {
		return at, true
	}
	if n := newlineLength(rest, at); n > 0 {
		return at + n, true
	}
	r, _ := utf8.DecodeRuneInString(rest[at:])
	return at, jsSpace(r)
}

func (s *scanner) dash() bool {
	rest := s.src[s.at:]
	if strings.HasPrefix(rest, "->>") {
		s.emit("->>", 3)
		return true
	}
	end, ok := blockEnd(rest, "---", "---")
	if ok {
		s.at += end
	}
	return ok
}

func (s *scanner) bracket(c byte) bool {
	rest := s.src[s.at:]
	if len(rest) < 2 || rest[1] != c {
		return false
	}
	s.emit(string([]byte{c, c}), 2)
	return true
}
