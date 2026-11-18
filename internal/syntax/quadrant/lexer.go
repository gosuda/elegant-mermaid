package quadrant

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
	modeTitle
	modeAccTitle
	modeAccDescr
	modeAccMulti
	modePointStart
	modePointX
	modePointY
	modeClassName
)

type scanner struct {
	src     string
	removed []source.Span
	deleted map[int]bool
	at      int
	opener  int
	modes   []lexMode
	tokens  []Token
}

func lex(src string, removed []source.Span) []Token {
	s := &scanner{src: src, removed: removed, deleted: deletedSemicolons(src), modes: []lexMode{modeInitial}}
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

func jsLineTerminator(r rune) bool { return r == '\n' || r == '\r' || r == 0x2028 || r == 0x2029 }

func foldByte(c byte) byte {
	if c >= 'A' && c <= 'Z' {
		return c + 'a' - 'A'
	}
	return c
}

func (s *scanner) mode() lexMode { return s.modes[len(s.modes)-1] }

func (s *scanner) pop() {
	if len(s.modes) > 1 {
		s.modes = s.modes[:len(s.modes)-1]
	}
}

func (s *scanner) push(m lexMode) { s.modes = append(s.modes, m) }

func (s *scanner) emit(kind string, length int) {
	end := min(s.at+length, len(s.src))
	span := source.Span{Start: s.at, End: end}
	s.tokens = append(s.tokens, Token{Kind: kind, Text: sub(s.src, s.at, end), Span: span, Content: span})
	s.at = end
}

func (s *scanner) quoted(kind, text string, span, content source.Span) {
	s.tokens = append(s.tokens, Token{Kind: kind, Text: text, Span: span, Content: content})
}

func (s *scanner) run() []Token {
	for s.at < len(s.src) {
		if end, ok := s.removedEnd(s.at); ok {
			s.at = end
			continue
		}
		if s.deleted[s.at] {
			s.at++
			continue
		}
		s.step()
	}
	s.finish()
	end := len(s.src)
	span := source.Span{Start: end, End: end}
	return append(s.tokens, Token{Kind: "EOF", Span: span, Content: span})
}

func (s *scanner) finish() {
	switch s.mode() {
	case modeTitle:
		s.emit("title_value", 0)
	case modeString:
		s.unterminated("\"", s.opener)
	case modeMarkdown:
		s.unterminated("\"`", s.opener)
	case modeAccMulti:
		s.unterminated("{", s.opener)
	case modePointStart, modePointX, modePointY:
		s.unterminated("[", s.opener)
	case modeClassName:
		s.unterminated(":::", s.opener)
	}
}

func (s *scanner) removedEnd(at int) (int, bool) {
	for _, span := range s.removed {
		if span.Start <= at && at < span.End {
			return span.End, true
		}
	}
	return 0, false
}

func (s *scanner) unterminated(opener string, start int) {
	span := source.Span{Start: start, End: len(s.src)}
	s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: opener, Span: span, Content: span})
	s.at = len(s.src)
	s.modes = []lexMode{modeInitial}
}

func (s *scanner) invalid() {
	s.modes = []lexMode{modeInitial}
	width := utf8RuneLen(s.src[s.at:])
	if isLineByte(s.src[s.at]) {
		width = 0
	}
	s.emit("INVALID", width)
}

func (s *scanner) step() {
	switch s.mode() {
	case modeString:
		s.lexString()
	case modeMarkdown:
		s.lexMarkdown()
	case modeTitle:
		s.lexLineValue("title_value")
	case modeAccTitle:
		s.lexLineValue("acc_title_value")
	case modeAccDescr:
		s.lexLineValue("acc_descr_value")
	case modeAccMulti:
		s.lexAccessibilityBlock()
	default:
		s.stepPoint()
	}
}

func (s *scanner) stepPoint() {
	switch s.mode() {
	case modePointStart:
		s.lexPointStart()
	case modePointX:
		s.lexPointX()
	case modePointY:
		s.lexPointY()
	case modeClassName:
		s.lexClassName()
	default:
		s.lexInitial()
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
		s.quoted("STR", rest[:i], source.Span{Start: s.opener, End: s.at + i + 1}, source.Span{Start: s.at, End: s.at + i})
	}
	s.at += i + 1
	s.pop()
}

func (s *scanner) lexMarkdown() {
	for j := s.at; j < len(s.src); j++ {
		switch s.src[j] {
		case '`':
			if j+1 < len(s.src) && s.src[j+1] == '"' {
				s.closeMarkdown(j)
				return
			}
		case '"':
		default:
			continue
		}
		s.at = j
		s.invalid()
		return
	}
	s.unterminated("\"`", s.opener)
}

func (s *scanner) closeMarkdown(close int) {
	if close > s.at {
		s.quoted("MD_STR", s.src[s.at:close], source.Span{Start: s.opener, End: close + 2}, source.Span{Start: s.at, End: close})
	}
	s.at = close + 2
	s.pop()
}

func (s *scanner) lexLineValue(kind string) {
	n := strings.IndexAny(s.src[s.at:], "\n\r")
	if n < 0 {
		n = len(s.src) - s.at
	}
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
		if !jsSpace(r) {
			break
		}
		n += size
	}
	return n
}

func (s *scanner) blanks(at int) int {
	n := 0
	for at+n < len(s.src) && s.src[at+n] == ' ' {
		n++
	}
	return n
}

func (s *scanner) matchFold(at int, word string) bool {
	if at < 0 || at+len(word) > len(s.src) {
		return false
	}
	for i := range len(word) {
		if foldByte(s.src[at+i]) != foldByte(word[i]) {
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

func (s *scanner) padded(word string) int {
	lead := s.blanks(s.at)
	if !s.matchFold(s.at+lead, word) {
		return 0
	}
	end := s.at + lead + len(word)
	return end + s.blanks(end) - s.at
}

func (s *scanner) delimiter() int {
	at := s.at + s.blanks(s.at)
	dashes := 0
	for at+dashes < len(s.src) && s.src[at+dashes] == '-' {
		dashes++
	}
	if dashes < 2 || at+dashes >= len(s.src) || s.src[at+dashes] != '>' {
		return 0
	}
	end := at + dashes + 1
	return end + s.blanks(end) - s.at
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

func (s *scanner) lexInitial() {
	if s.lexSkip() || s.lexNewline() || s.lexAccessibility() || s.lexKeyword() || s.lexQuote() || s.lexPoint() || s.lexText() {
		return
	}
	s.emit("INVALID", utf8RuneLen(s.src[s.at:]))
}

func utf8RuneLen(text string) int {
	_, size := utf8.DecodeRuneInString(text)
	return max(size, 1)
}

func (s *scanner) skipLine(from int) {
	n := strings.IndexAny(s.src[from:], "\n\r")
	if n < 0 {
		n = len(s.src) - from
	}
	s.at = from + n
}

func (s *scanner) lexSkip() bool {
	rest := s.src[s.at:]
	if strings.HasPrefix(rest, "%%") {
		s.skipLine(s.at + 2)
		return true
	}
	r, size := utf8.DecodeRuneInString(rest)
	_, hidden := s.removedEnd(s.at + size)
	if r != '}' && !hidden && strings.HasPrefix(rest[size:], "%%") {
		s.skipLine(s.at + size + 2)
		return true
	}
	return false
}

func (s *scanner) lexNewline() bool {
	if !isLineByte(s.src[s.at]) {
		return false
	}
	n := 1
	for s.at+n < len(s.src) && isLineByte(s.src[s.at+n]) {
		n++
	}
	s.emit("NEWLINE", n)
	return true
}

func (s *scanner) open(kind string, length int, mode lexMode) bool {
	s.emit(kind, length)
	s.push(mode)
	return true
}

func (s *scanner) lexAccessibility() bool {
	if s.word("title") {
		return s.open("title", len("title"), modeTitle)
	}
	if n := s.accessibilityOpener("acctitle", ':'); n > 0 {
		return s.open("acc_title", n, modeAccTitle)
	}
	if n := s.accessibilityOpener("accdescr", ':'); n > 0 {
		return s.open("acc_descr", n, modeAccDescr)
	}
	n := s.accessibilityOpener("accdescr", '{')
	if n == 0 {
		return false
	}
	s.opener = s.at + strings.IndexByte(s.src[s.at:s.at+n], '{')
	s.at += n
	s.push(modeAccMulti)
	return true
}

func (s *scanner) lexKeyword() bool {
	for _, kw := range [...]struct{ word, kind string }{
		{"x-axis", "X-AXIS"}, {"y-axis", "Y-AXIS"},
	} {
		if n := s.padded(kw.word); n > 0 {
			s.emit(kw.kind, n)
			return true
		}
	}
	if n := s.delimiter(); n > 0 {
		s.emit("AXIS-TEXT-DELIMITER", n)
		return true
	}
	for _, kw := range [...]struct{ word, kind string }{
		{"quadrant-1", "QUADRANT_1"}, {"quadrant-2", "QUADRANT_2"}, {"quadrant-3", "QUADRANT_3"}, {"quadrant-4", "QUADRANT_4"},
	} {
		if n := s.padded(kw.word); n > 0 {
			s.emit(kw.kind, n)
			return true
		}
	}
	if s.word("classDef") {
		s.emit("CLASSDEF", len("classDef"))
		return true
	}
	return false
}

func (s *scanner) lexQuote() bool {
	if s.src[s.at] != '"' {
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

func (s *scanner) lexPoint() bool {
	if strings.HasPrefix(s.src[s.at:], ":::") {
		s.opener = s.at
		s.at += 3
		s.push(modeClassName)
		return true
	}
	at := s.at + s.spaces(s.at)
	if at >= len(s.src) || s.src[at] != ':' {
		return s.lexHeader()
	}
	at++
	at += s.spaces(at)
	if at >= len(s.src) || s.src[at] != '[' {
		return s.lexHeader()
	}
	s.opener = at
	at++
	at += s.spaces(at)
	return s.open("point_start", at-s.at, modePointStart)
}

func (s *scanner) lexHeader() bool {
	if n := s.padded("quadrantChart"); n > 0 {
		s.emit("QUADRANT", n)
		return true
	}
	return false
}

var punctuation = map[byte]string{
	':': "COLON", '+': "PLUS", ',': "COMMA", '=': "EQUALS", '*': "MULT", '#': "BRKT",
	'_': "UNDERSCORE", '.': "DOT", '&': "AMP", '-': "MINUS", ';': "SEMI",
}

const otherPunctuation = "!$%'`?\\/"

func (s *scanner) lexText() bool {
	c := s.src[s.at]
	switch {
	case isLetter(c):
		s.emit("ALPHA", s.runOf(isLetter))
	case c >= utf8.RuneSelf:
		s.emit("UNICODE_TEXT", s.nonASCII())
	case isDigit(c):
		s.emit("NUM", s.runOf(isDigit))
	case s.entityEnd(s.at) > 0:
		s.emit("UNICODE_TEXT", s.entityEnd(s.at))
	default:
		return s.lexSingle(c)
	}
	return true
}

func (s *scanner) runOf(in func(byte) bool) int {
	n := 1
	for s.at+n < len(s.src) && in(s.src[s.at+n]) {
		n++
	}
	return n
}

func (s *scanner) nonASCII() int {
	n := 0
	for s.at+n < len(s.src) && s.src[s.at+n] >= utf8.RuneSelf {
		n++
	}
	return n
}

func (s *scanner) lexSingle(c byte) bool {
	if kind, ok := punctuation[c]; ok {
		s.emit(kind, 1)
		return true
	}
	switch {
	case c == ' ' || c == '\t' || c == '\v' || c == '\f':
		s.emit("SPACE", 1)
	case strings.IndexByte(otherPunctuation, c) >= 0:
		s.emit("PUNCTUATION", 1)
	default:
		return false
	}
	return true
}

func (s *scanner) coordinate(at int) int {
	if at >= len(s.src) {
		return 0
	}
	switch s.src[at] {
	case '1':
		return 1
	case '0':
		return 1 + s.fraction(at+1)
	}
	return 0
}

func (s *scanner) fraction(at int) int {
	if at >= len(s.src) {
		return 0
	}
	r, size := utf8.DecodeRuneInString(s.src[at:])
	if jsLineTerminator(r) || r > 0xffff {
		return 0
	}
	digits := 0
	for at+size+digits < len(s.src) && isDigit(s.src[at+size+digits]) {
		digits++
	}
	if digits == 0 {
		return 0
	}
	return size + digits
}

func (s *scanner) lexPointStart() {
	if n := s.coordinate(s.at); n > 0 {
		s.emit("point_x", n)
		s.push(modePointX)
		return
	}
	at := s.at + s.spaces(s.at)
	if at >= len(s.src) || s.src[at] != ']' {
		s.invalid()
		return
	}
	at++
	s.at = at + s.blanks(at)
	s.pop()
}

func (s *scanner) lexPointX() {
	at := s.at + s.spaces(s.at)
	if at >= len(s.src) || s.src[at] != ',' {
		s.invalid()
		return
	}
	at++
	s.at = at + s.spaces(at)
	s.pop()
	s.push(modePointY)
}

func (s *scanner) lexPointY() {
	n := s.coordinate(s.at)
	if n == 0 {
		s.invalid()
		return
	}
	s.pop()
	s.emit("point_y", n)
}

func (s *scanner) lexClassName() {
	if !isWordByte(s.src[s.at]) {
		s.invalid()
		return
	}
	n := s.runOf(isWordByte)
	s.pop()
	s.emit("class_name", n)
}
