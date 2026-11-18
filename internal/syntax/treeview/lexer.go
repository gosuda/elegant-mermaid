package treeview

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	headerWord = "treeView-beta"

	kindHeader       = headerWord
	kindAccDescr     = "ACC_DESCR"
	kindAccTitle     = "ACC_TITLE"
	kindTitle        = "TITLE"
	kindClass        = "CLASS_ANNOTATION"
	kindIcon         = "ICON_ANNOTATION"
	kindDesc         = "DESC_ANNOTATION"
	kindIndent       = "INDENTATION"
	kindQuoted       = "QUOTED_NAME"
	kindBare         = "BARE_NAME"
	kindEOF          = "EOF"
	kindInvalid      = "INVALID"
	kindUnterminated = "UNTERMINATED"
)

type scanner struct {
	text string
	orig []int
	end  int
	at   int
}

type rule struct {
	kind   string
	hidden bool
	match  func(*scanner, int) int
}

var rules = []rule{
	{kind: kindHeader, match: (*scanner).header},
	{kind: kindAccDescr, match: (*scanner).accDescr},
	{kind: kindAccTitle, match: (*scanner).accTitle},
	{kind: kindTitle, match: (*scanner).title},
	{kind: kindClass, match: (*scanner).class},
	{kind: kindIcon, match: (*scanner).icon},
	{kind: kindDesc, match: (*scanner).desc},
	{kind: kindIndent, match: (*scanner).indent},
	{kind: kindQuoted, match: (*scanner).quoted},
	{hidden: true, match: (*scanner).comment},
	{hidden: true, match: (*scanner).newline},
	{kind: kindBare, match: (*scanner).bare},
}

func newScanner(src string, removed []source.Span) (*scanner, []diag.Diagnostic) {
	text, orig := prepare(src, removed)
	text, orig, diags := convertBox(text, orig, len(src))
	return &scanner{text: text, orig: orig, end: len(src)}, diags
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
	text := s.text[from:to]
	return Token{Kind: kind, Text: text, Value: tokenValue(kind, text), Span: s.span(from, to), from: from, to: to}
}

func tokenValue(kind, text string) string {
	switch kind {
	case kindAccDescr:
		return accDescrValue(text)
	case kindAccTitle:
		return accTitleValue(text)
	case kindTitle:
		return titleValue(text)
	case kindClass:
		return classValue(text)
	case kindIcon:
		return iconValue(text)
	case kindDesc:
		return descValue(text)
	case kindQuoted, kindBare:
		return nameValue(kind, text)
	}
	return text
}

func (s *scanner) next() Token {
	for s.at < len(s.text) {
		if token, ok := s.attempt(s.at); ok {
			return token
		}
	}
	return Token{Kind: kindEOF, Span: source.Span{Start: s.end, End: s.end}, from: len(s.text), to: len(s.text)}
}

func (s *scanner) attempt(at int) (Token, bool) {
	for _, r := range rules {
		end := r.match(s, at)
		if end < 0 {
			continue
		}
		if r.hidden {
			s.at = end
			return Token{}, false
		}
		return s.token(r.kind, at, end), true
	}
	return s.reject(at), true
}

func (s *scanner) reject(at int) Token {
	c := s.text[at]
	if c == '"' || c == '\'' {
		s.at = len(s.text)
		return Token{Kind: kindUnterminated, Text: string(c), Span: source.Span{Start: s.start(at), End: s.end}, from: at, to: len(s.text)}
	}
	_, size := utf8.DecodeRuneInString(s.text[at:])
	return s.token(kindInvalid, at, at+size)
}

func (s *scanner) lineEnd(from int) int {
	if end := strings.IndexByte(s.text[min(from, len(s.text)):], '\n'); end >= 0 {
		return from + end
	}
	return len(s.text)
}

func (s *scanner) has(at int, literal string) bool {
	return strings.HasPrefix(s.text[at:], literal)
}

func (s *scanner) blanks(at int) int {
	for at < len(s.text) && blank(s.text[at]) {
		at++
	}
	return at
}

func (s *scanner) tail(at int) int {
	for at < len(s.text) && s.text[at] != '\n' && s.text[at] != '\r' {
		if s.has(at, "%%") {
			return at
		}
		at++
	}
	return at
}

func (s *scanner) header(at int) int {
	end := at + len(headerWord)
	if !s.has(at, headerWord) {
		return -1
	}
	if end < len(s.text) && !s.has(end, "%%") {
		if r, _ := utf8.DecodeRuneInString(s.text[end:]); !jsSpace(r) {
			return -1
		}
	}
	if s.bare(at) > end {
		return -1
	}
	return end
}

func (s *scanner) accDescr(at int) int {
	q := s.blanks(at)
	if !s.has(q, "accDescr") {
		return -1
	}
	q += len("accDescr")
	if r := s.blanks(q); r < len(s.text) && s.text[r] == ':' {
		return s.tail(r + 1)
	}
	r := q
	for r < len(s.text) {
		c, n := utf8.DecodeRuneInString(s.text[r:])
		if !jsSpace(c) {
			break
		}
		r += n
	}
	if r >= len(s.text) || s.text[r] != '{' {
		return -1
	}
	if closing := strings.IndexByte(s.text[r+1:], '}'); closing >= 0 {
		return r + 1 + closing + 1
	}
	return -1
}

func (s *scanner) accTitle(at int) int {
	q := s.blanks(at)
	if !s.has(q, "accTitle") {
		return -1
	}
	q = s.blanks(q + len("accTitle"))
	if q >= len(s.text) || s.text[q] != ':' {
		return -1
	}
	return s.tail(q + 1)
}

func (s *scanner) title(at int) int {
	q := s.blanks(at)
	if !s.has(q, "title") {
		return -1
	}
	q += len("title")
	if q < len(s.text) && blank(s.text[q]) {
		return s.tail(q + 1)
	}
	return q
}

func (s *scanner) annotation(at int) int {
	q := s.blanks(at)
	if q == at {
		return -1
	}
	return q
}

func (s *scanner) wordRun(at int) int {
	for at < len(s.text) && (wordChar(s.text[at]) || s.text[at] == '-') {
		at++
	}
	return at
}

func (s *scanner) class(at int) int {
	q := s.annotation(at)
	if q < 0 || !s.has(q, ":::") {
		return -1
	}
	q = s.blanks(q + len(":::"))
	if q >= len(s.text) || s.text[q] != '_' && (s.text[q] < 'a' || s.text[q] > 'z') && (s.text[q] < 'A' || s.text[q] > 'Z') {
		return -1
	}
	return s.wordRun(q + 1)
}

func (s *scanner) icon(at int) int {
	q := s.annotation(at)
	if q < 0 || !s.has(q, "icon(") {
		return -1
	}
	q = s.wordRun(q + len("icon("))
	if q < len(s.text) && s.text[q] == ':' {
		name := s.wordRun(q + 1)
		if name == q+1 {
			return -1
		}
		q = name
	}
	if q >= len(s.text) || s.text[q] != ')' {
		return -1
	}
	return q + 1
}

func (s *scanner) desc(at int) int {
	q := s.annotation(at)
	if q < 0 || !s.has(q, "##") {
		return -1
	}
	return s.lineEndOrCarriage(q + len("##"))
}

func (s *scanner) lineEndOrCarriage(at int) int {
	for at < len(s.text) && s.text[at] != '\n' && s.text[at] != '\r' {
		at++
	}
	return at
}

func (s *scanner) indent(at int) int { return s.annotation(at) }

func (s *scanner) quoted(at int) int {
	c := s.text[at]
	if c != '"' && c != '\'' {
		return -1
	}
	closing := strings.IndexByte(s.text[at+1:], c)
	if closing < 0 {
		return -1
	}
	return at + 1 + closing + 1
}

func (s *scanner) comment(at int) int {
	if !s.has(at, "%%") {
		return -1
	}
	return s.lineEnd(at)
}

func (s *scanner) newline(at int) int {
	if s.text[at] != '\n' {
		return -1
	}
	return at + 1
}

func (s *scanner) marker(at int) bool {
	q := s.blanks(at)
	if q == at {
		return false
	}
	if s.has(q, "icon(") || s.has(q, "##") {
		return true
	}
	return s.has(q, ":::") && s.classStart(s.blanks(q+len(":::")))
}

func (s *scanner) classStart(at int) bool {
	if at >= len(s.text) {
		return false
	}
	c := s.text[at]
	return c == '_' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z'
}

func (s *scanner) bare(at int) int {
	if at >= len(s.text) {
		return -1
	}
	switch c := s.text[at]; c {
	case ' ', '\t', '\n', '\r', '"', '\'':
		return -1
	}
	if s.has(at, ":::") || s.has(at, "icon(") || s.has(at, "##") {
		return -1
	}
	_, size := utf8.DecodeRuneInString(s.text[at:])
	q := at + size
	for q < len(s.text) && s.text[q] != '\n' && s.text[q] != '\r' && !s.marker(q) {
		q++
	}
	return q
}
