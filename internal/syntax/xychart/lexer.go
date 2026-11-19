package xychart

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type lexMode uint8

const (
	modeInitial lexMode = iota
	modeString
	modeMarkdown
	modeAccTitle
	modeAccDescr
	modeAccMulti
	modeAxisData
	modeAxisBand
	modeData
	modeDataInner
)

type scanner struct {
	src     string
	removed []source.Span
	at      int
	opener  int
	modes   []lexMode
	tokens  []Token
}

func lex(src string, removed []source.Span) []Token {
	s := &scanner{src: src, removed: removed, modes: []lexMode{modeInitial}}
	return s.run()
}

func sub(text string, from, to int) string {
	if from < 0 || to < from || to > len(text) {
		return ""
	}
	if from < len(text) && !utf8.RuneStart(text[from]) {
		return ""
	}
	if to < len(text) && !utf8.RuneStart(text[to]) {
		return ""
	}
	return text[from:to]
}

func isWordByte(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func isLetter(c byte) bool { return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' }

func isLineByte(c byte) bool { return c == '\n' || c == '\r' }

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func foldByte(c byte) byte {
	if c >= 'A' && c <= 'Z' {
		return c + 'a' - 'A'
	}
	return c
}

func (s *scanner) mode() lexMode {
	if len(s.modes) == 0 {
		return modeInitial
	}
	return s.modes[len(s.modes)-1]
}

func (s *scanner) pop() {
	if len(s.modes) > 0 {
		s.modes = s.modes[:len(s.modes)-1]
	}
}

func (s *scanner) push(m lexMode) { s.modes = append(s.modes, m) }

func (s *scanner) emit(kind string, length int) {
	end := min(s.at+length, len(s.src))
	s.tokens = append(s.tokens, Token{Kind: kind, Text: sub(s.src, s.at, end), Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) value(kind, text string, start, end int) {
	s.tokens = append(s.tokens, Token{Kind: kind, Text: text, Span: source.Span{Start: start, End: end}})
}

func (s *scanner) run() []Token {
	for s.at < len(s.src) {
		if end, ok := s.removedEnd(); ok {
			s.at = end
			continue
		}
		s.step()
	}
	end := len(s.src)
	return append(s.tokens, Token{Kind: "EOF", Span: source.Span{Start: end, End: end}})
}

func (s *scanner) removedEnd() (int, bool) {
	for _, span := range s.removed {
		if span.Start <= s.at && s.at < span.End {
			return span.End, true
		}
	}
	return 0, false
}

func (s *scanner) unterminated(opener string, start int) {
	s.value("UNTERMINATED", opener, start, len(s.src))
	s.at = len(s.src)
}

func (s *scanner) step() {
	switch s.mode() {
	case modeString:
		s.lexString()
	case modeMarkdown:
		s.lexMarkdown()
	case modeAccTitle:
		s.lexAccessibilityValue("acc_title_value")
	case modeAccDescr:
		s.lexAccessibilityValue("acc_descr_value")
	case modeAccMulti:
		s.lexAccessibilityBlock()
	default:
		s.lexInclusive()
	}
}

func (s *scanner) lexString() {
	rest := s.src[s.at:]
	i := strings.IndexByte(rest, '"')
	if i < 0 {
		s.unterminated("\"", s.opener)
		return
	}
	if i > 0 {
		s.value("STR", rest[:i], s.opener, s.at+i+1)
	}
	s.at += i + 1
	s.pop()
}

func (s *scanner) lexMarkdown() {
	rest := s.src[s.at:]
	line := len(rest)
	if i := strings.IndexAny(rest, "\n\r\u2028\u2029"); i >= 0 {
		line = i
	}
	i := strings.Index(rest[:line], "`\"")
	if i < 0 {
		s.unterminated("\"`", s.opener)
		return
	}
	if i > 0 {
		s.value("MD_STR", rest[:i], s.opener, s.at+i+2)
	}
	s.at += i + 2
	s.pop()
}

func (s *scanner) lineEnd() int {
	rest := s.src[s.at:]
	if i := strings.IndexAny(rest, "\n\r"); i >= 0 {
		return i
	}
	return len(rest)
}

func (s *scanner) lexAccessibilityValue(kind string) {
	n := s.lineEnd()
	s.emit(kind, n)
	s.pop()
}

func (s *scanner) lexAccessibilityBlock() {
	if s.src[s.at] == '}' {
		s.at++
		s.pop()
		return
	}
	i := strings.IndexByte(s.src[s.at:], '}')
	if i < 0 {
		s.unterminated("{", s.opener)
		return
	}
	s.emit("acc_descr_multiline_value", i)
}

func (s *scanner) spaces(at int) int {
	n := 0
	for at+n < len(s.src) {
		r, size := utf8.DecodeRuneInString(s.src[at+n:])
		if size == 0 || !jsSpace(r) {
			break
		}
		n += size
	}
	return n
}

func (s *scanner) matchFold(at int, word string) bool {
	if at+len(word) > len(s.src) {
		return false
	}
	for i := range len(word) {
		if foldByte(s.src[at+i]) != word[i] {
			return false
		}
	}
	return true
}

func (s *scanner) word(word string) bool {
	if !s.matchFold(s.at, word) {
		return false
	}
	end := s.at + len(word)
	return end >= len(s.src) || !isWordByte(s.src[end])
}

func (s *scanner) accessibilityOpener(word string, separator byte) int {
	if !s.matchFold(s.at, word) {
		return 0
	}
	at := s.at + len(word)
	at += s.spaces(at)
	if at >= len(s.src) || s.src[at] != separator {
		return 0
	}
	at++
	at += s.spaces(at)
	return at - s.at
}

func (s *scanner) number(at int) int {
	start := at
	if at < len(s.src) && (s.src[at] == '+' || s.src[at] == '-') {
		at++
	}
	if end := s.digitsEnd(at); end > at {
		return s.fractionEnd(end) - start
	}
	if end := s.fractionEnd(at); end > at {
		return end - start
	}
	return 0
}

func (s *scanner) digitsEnd(at int) int {
	for at < len(s.src) && isDigit(s.src[at]) {
		at++
	}
	return at
}

func (s *scanner) fractionEnd(at int) int {
	if at+1 < len(s.src) && s.src[at] == '.' && isDigit(s.src[at+1]) {
		return s.digitsEnd(at + 1)
	}
	return at
}

func (s *scanner) lexInclusive() {
	c := s.src[s.at]
	mode := s.mode()
	if isLineByte(c) {
		s.lexNewline(mode, c)
		return
	}
	if s.lexKeyword(mode) || s.lexData(mode, c) || s.lexQuote(c) || s.lexPlain(c) {
		return
	}
	s.emit("INVALID", utf8RuneLen(s.src[s.at:]))
}

func (s *scanner) lexNewline(mode lexMode, c byte) {
	n := 1
	if mode == modeAxisData || mode == modeData {
		if c == '\r' && s.at+1 < len(s.src) && s.src[s.at+1] == '\n' {
			n = 2
		}
		s.pop()
		s.emit("NEWLINE", n)
		return
	}
	for s.at+n < len(s.src) && isLineByte(s.src[s.at+n]) {
		n++
	}
	s.emit("NEWLINE", n)
}

func utf8RuneLen(text string) int {
	_, size := utf8.DecodeRuneInString(text)
	return max(size, 1)
}

func (s *scanner) lexKeyword(mode lexMode) bool {
	if s.word("title") {
		s.emit("title", len("title"))
		return true
	}
	if n := s.accessibilityOpener("acctitle", ':'); n > 0 {
		s.emit("acc_title", n)
		s.push(modeAccTitle)
		return true
	}
	if n := s.accessibilityOpener("accdescr", ':'); n > 0 {
		s.emit("acc_descr", n)
		s.push(modeAccDescr)
		return true
	}
	if n := s.accessibilityOpener("accdescr", '{'); n > 0 {
		s.opener = s.at + strings.IndexByte(s.src[s.at:s.at+n], '{')
		s.at += n
		s.push(modeAccMulti)
		return true
	}
	for _, kw := range []struct {
		text string
		kind string
		mode lexMode
	}{{"xychart-beta", "XYCHART", modeInitial}, {"xychart", "XYCHART", modeInitial}, {"x-axis", "X_AXIS", modeAxisData}, {"y-axis", "Y_AXIS", modeAxisData}} {
		if s.word(kw.text) {
			s.emit(kw.kind, len(kw.text))
			if kw.mode != modeInitial {
				s.push(kw.mode)
			}
			return true
		}
	}
	for _, orientation := range []string{"vertical", "horizontal"} {
		if s.matchFold(s.at, orientation) {
			s.emit("CHART_ORIENTATION", len(orientation))
			return true
		}
	}
	return false
}

func (s *scanner) lexData(mode lexMode, c byte) bool {
	switch {
	case mode == modeAxisData && c == '[':
		s.emit("SQUARE_BRACES_START", 1)
		s.push(modeAxisBand)
	case mode == modeAxisData && strings.HasPrefix(s.src[s.at:], "-->"):
		s.emit("ARROW_DELIMITER", 3)
	case s.word("line"):
		s.emit("LINE", len("line"))
		s.push(modeData)
	case s.word("bar"):
		s.emit("BAR", len("bar"))
		s.push(modeData)
	case mode == modeData && c == '[':
		s.emit("SQUARE_BRACES_START", 1)
		s.push(modeDataInner)
	default:
		return s.lexNumber(mode, c)
	}
	return true
}

func (s *scanner) lexNumber(mode lexMode, c byte) bool {
	if mode == modeAxisData || mode == modeDataInner {
		if n := s.number(s.at); n > 0 {
			s.emit("NUMBER_WITH_DECIMAL", n)
			return true
		}
	}
	return s.lexClose(mode, c)
}

func (s *scanner) lexClose(mode lexMode, c byte) bool {
	if c == ']' && (mode == modeDataInner || mode == modeAxisBand) {
		s.emit("SQUARE_BRACES_END", 1)
		s.pop()
		return true
	}
	return false
}

func (s *scanner) lexQuote(c byte) bool {
	if c != '"' {
		return false
	}
	s.opener = s.at
	if s.at+1 < len(s.src) && s.src[s.at+1] == '`' {
		s.at += 2
		s.push(modeMarkdown)
		return true
	}
	s.at++
	s.push(modeString)
	return true
}

var punctuation = map[byte]string{
	'[': "SQUARE_BRACES_START", ']': "SQUARE_BRACES_END", ':': "COLON", '+': "PLUS", ',': "COMMA",
	'=': "EQUALS", '*': "MULT", '#': "BRKT", '_': "UNDERSCORE", '.': "DOT", '&': "AMP", '-': "MINUS",
	';': "SEMI",
}

func (s *scanner) lexPlain(c byte) bool {
	if kind, ok := punctuation[c]; ok {
		s.emit(kind, 1)
		return true
	}
	switch {
	case isLetter(c):
		n := 1
		for s.at+n < len(s.src) && isLetter(s.src[s.at+n]) {
			n++
		}
		s.emit("ALPHA", n)
	case isDigit(c):
		n := 1
		for s.at+n < len(s.src) && isDigit(s.src[s.at+n]) {
			n++
		}
		s.emit("NUM", n)
	default:
		n := s.spaces(s.at)
		if n == 0 {
			return false
		}
		s.at += n
	}
	return true
}
