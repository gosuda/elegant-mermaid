package journey

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type lexMode uint8

const (
	modeInitial lexMode = iota
	modeAccTitle
	modeAccDescr
	modeAccDescrMultiline
)

const (
	kindJourney   = "journey"
	kindNewline   = "NEWLINE"
	kindTitle     = "title"
	kindAccTitle  = "acc_title"
	kindAccTitleV = "acc_title_value"
	kindAccDescr  = "acc_descr"
	kindAccDescrV = "acc_descr_value"
	kindOpen      = "acc_descr_open"
	kindMultiline = "acc_descr_multiline_value"
	kindClose     = "acc_descr_close"
	kindSection   = "section"
	kindTaskName  = "taskName"
	kindTaskData  = "taskData"
	kindColon     = ":"
	kindEOF       = "EOF"
	kindInvalid   = "INVALID"
	kindUnclosed  = "UNTERMINATED"
)

func IsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xA0, 0x1680, 0x2028, 0x2029, 0x202F, 0x205F, 0x3000, 0xFEFF:
		return true
	}
	return r >= 0x2000 && r <= 0x200A
}

func Trim(text string) string {
	lo, hi := trimBounds(text)
	return text[lo:hi]
}

func trimBounds(text string) (int, int) {
	lo, hi := 0, len(text)
	for lo < hi {
		r, size := utf8.DecodeRuneInString(text[lo:hi])
		if !IsSpace(r) {
			break
		}
		lo += size
	}
	for hi > lo {
		r, size := utf8.DecodeLastRuneInString(text[lo:hi])
		if !IsSpace(r) {
			break
		}
		hi -= size
	}
	return lo, hi
}

func spaceRun(text string) int {
	n := 0
	for n < len(text) {
		r, size := utf8.DecodeRuneInString(text[n:])
		if !IsSpace(r) {
			break
		}
		n += size
	}
	return n
}

func foldPrefix(text, word string) bool {
	if len(text) < len(word) {
		return false
	}
	for i := range len(word) {
		c := text[i]
		if c >= 'A' && c <= 'Z' {
			c += 'a' - 'A'
		}
		if c != word[i] {
			return false
		}
	}
	return true
}

func isWord(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func entityLength(text string) int {
	n := 1
	for n < len(text) && isWord(text[n]) {
		n++
	}
	if n == 1 || n >= len(text) || text[n] != ';' {
		return 0
	}
	return n + 1
}

func runUntil(text, stop string) int {
	protect := strings.IndexByte(stop, '#') >= 0
	for i := 0; i < len(text); {
		if protect && text[i] == '#' {
			if n := entityLength(text[i:]); n > 0 {
				i += n
				continue
			}
		}
		if strings.IndexByte(stop, text[i]) >= 0 {
			return i
		}
		i++
	}
	return len(text)
}

type view struct {
	text   string
	from   []int
	to     []int
	length int
}

func newView(src string, removed []source.Span) *view {
	bytes := make([]byte, 0, len(src))
	v := &view{length: len(src)}
	add := func(c byte, from, to int) {
		bytes = append(bytes, c)
		v.from = append(v.from, from)
		v.to = append(v.to, to)
	}
	next := 0
	for i := 0; i < len(src); {
		for next < len(removed) && removed[next].End <= i {
			next++
		}
		if next < len(removed) && removed[next].Start <= i {
			i = min(removed[next].End, len(src))
			continue
		}
		switch {
		case src[i] == '\r' && i+1 < len(src) && src[i+1] == '\n':
			add('\n', i, i+2)
			i += 2
		case src[i] == '\r':
			add('\n', i, i+1)
			i++
		default:
			add(src[i], i, i+1)
			i++
		}
	}
	v.text = string(bytes)
	return v
}

func (v *view) offset(at int) int {
	if at < len(v.from) {
		return v.from[at]
	}
	return v.length
}

func (v *view) span(from, to int) source.Span {
	if to > from {
		return source.Span{Start: v.from[from], End: v.to[to-1]}
	}
	at := v.offset(from)
	return source.Span{Start: at, End: at}
}

func (v *view) value(from, to int) Value {
	return Value{Text: v.text[from:to], Span: v.span(from, to)}
}

type scanner struct {
	v       *view
	at      int
	mode    lexMode
	opener  int
	lineEnd int
	tokens  []Token
}

func lex(v *view) []Token {
	s := &scanner{v: v, lineEnd: -1}
	for s.step() {
	}
	return s.tokens
}

func (s *scanner) step() bool {
	switch s.mode {
	case modeAccTitle:
		s.accValue(kindAccTitleV)
	case modeAccDescr:
		s.accValue(kindAccDescrV)
	case modeAccDescrMultiline:
		return s.multiline()
	default:
		if s.at >= len(s.v.text) {
			s.emit(kindEOF, s.at, s.at)
			return false
		}
		s.initial()
	}
	return true
}

func (s *scanner) physicalEnd(at int) int {
	if s.lineEnd < at {
		s.lineEnd = at + runUntil(s.v.text[at:], "\n")
	}
	return s.v.offset(s.lineEnd)
}

func (s *scanner) emit(kind string, from, to int) *Token {
	value := s.v.value(from, to)
	s.tokens = append(s.tokens, Token{Kind: kind, Text: value.Text, Span: value.Span, Value: value, end: s.physicalEnd(from)})
	s.at = to
	return &s.tokens[len(s.tokens)-1]
}

func (s *scanner) accValue(kind string) {
	rest := s.v.text[s.at:]
	s.emit(kind, s.at, s.at+runUntil(rest, "\n"))
	s.mode = modeInitial
}

func (s *scanner) multiline() bool {
	rest := s.v.text[s.at:]
	switch {
	case rest == "":
		start := s.v.offset(s.opener)
		s.tokens = append(s.tokens, Token{Kind: kindUnclosed, Text: "{", Span: source.Span{Start: start, End: s.v.length}, end: s.v.length})
		return false
	case rest[0] == '}':
		s.emit(kindClose, s.at, s.at+1)
		s.mode = modeInitial
	default:
		s.emit(kindMultiline, s.at, s.at+runUntil(rest, "}"))
	}
	return true
}

func (s *scanner) skip(length int) { s.at += length }

func (s *scanner) initial() {
	rest := s.v.text[s.at:]
	if s.comment(rest) || s.newline(rest) || s.whitespace(rest) || s.hashComment(rest) {
		return
	}
	if s.header(rest) || s.titleLine(rest) || s.accessibility(rest) || s.sectionLine(rest) || s.task(rest) {
		return
	}
	_, size := utf8.DecodeRuneInString(rest)
	s.emit(kindInvalid, s.at, s.at+size)
}

func (s *scanner) comment(rest string) bool {
	if strings.HasPrefix(rest, "%%") && !strings.HasPrefix(rest[2:], "{") {
		s.skip(2 + runUntil(rest[2:], "\n"))
		return true
	}
	r, size := utf8.DecodeRuneInString(rest)
	if r == '}' || r >= 0x10000 || !strings.HasPrefix(rest[size:], "%%") {
		return false
	}
	s.skip(size + 2 + runUntil(rest[size+2:], "\n"))
	return true
}

func (s *scanner) newline(rest string) bool {
	if rest[0] != '\n' {
		return false
	}
	n := 1
	for n < len(rest) && rest[n] == '\n' {
		n++
	}
	s.emit(kindNewline, s.at, s.at+n)
	return true
}

func (s *scanner) whitespace(rest string) bool {
	n := spaceRun(rest)
	s.skip(n)
	return n > 0
}

func (s *scanner) hashComment(rest string) bool {
	if rest[0] != '#' || entityLength(rest) > 0 {
		return false
	}
	s.skip(runUntil(rest, "\n"))
	return true
}

func (s *scanner) header(rest string) bool {
	const word = "journey"
	if !foldPrefix(rest, word) || len(rest) > len(word) && isWord(rest[len(word)]) {
		return false
	}
	s.emit(kindJourney, s.at, s.at+len(word))
	return true
}

func keywordLine(rest, word, stop string) (lead, total int, ok bool) {
	if !foldPrefix(rest, word) {
		return 0, 0, false
	}
	r, size := utf8.DecodeRuneInString(rest[len(word):])
	if size == 0 || !IsSpace(r) {
		return 0, 0, false
	}
	lead = len(word) + size
	n := runUntil(rest[lead:], stop)
	if n == 0 {
		return 0, 0, false
	}
	return lead, lead + n, true
}

func (s *scanner) valueToken(kind string, lead, total int) {
	token := s.emit(kind, s.at, s.at+total)
	token.Value = s.v.value(s.at-total+lead, s.at)
}

func (s *scanner) titleLine(rest string) bool {
	lead, total, ok := keywordLine(rest, "title", "#\n;")
	if ok {
		s.valueToken(kindTitle, lead, total)
	}
	return ok
}

func (s *scanner) sectionLine(rest string) bool {
	lead, total, ok := keywordLine(rest, "section", "#:\n;")
	if ok {
		s.valueToken(kindSection, lead, total)
	}
	return ok
}

func accessLead(rest, word string, delimiter byte) (head, tail int, ok bool) {
	if !foldPrefix(rest, word) {
		return 0, 0, false
	}
	head = len(word) + spaceRun(rest[len(word):])
	if head >= len(rest) || rest[head] != delimiter {
		return 0, 0, false
	}
	return head, head + 1 + spaceRun(rest[head+1:]), true
}

func (s *scanner) accessibility(rest string) bool {
	if _, total, ok := accessLead(rest, "acctitle", ':'); ok {
		s.emit(kindAccTitle, s.at, s.at+total)
		s.mode = modeAccTitle
		return true
	}
	if _, total, ok := accessLead(rest, "accdescr", ':'); ok {
		s.emit(kindAccDescr, s.at, s.at+total)
		s.mode = modeAccDescr
		return true
	}
	if head, total, ok := accessLead(rest, "accdescr", '{'); ok {
		s.opener = s.at + head
		s.emit(kindOpen, s.opener, s.opener+1)
		s.at += total - head - 1
		s.mode = modeAccDescrMultiline
		return true
	}
	return false
}

func (s *scanner) task(rest string) bool {
	switch n := runUntil(rest, "#:\n;"); {
	case n > 0:
		s.emit(kindTaskName, s.at, s.at+n)
	case rest[0] != ':':
		return false
	default:
		s.taskData(rest)
	}
	return true
}

func (s *scanner) taskData(rest string) {
	n := runUntil(rest[1:], "#\n;")
	if n == 0 {
		s.emit(kindColon, s.at, s.at+1)
		return
	}
	start := s.at
	token := s.emit(kindTaskData, start, start+1+n)
	token.Fields = s.fields(start+1, start+1+n)
}

func (s *scanner) fields(from, to int) []Field {
	var out []Field
	for {
		end := from + runUntil(s.v.text[from:to], ":")
		out = append(out, s.field(from, end))
		if end >= to {
			return out
		}
		from = end + 1
	}
}

func (s *scanner) field(from, to int) Field {
	raw := s.v.value(from, to)
	lo, hi := trimBounds(s.v.text[from:to])
	if lo == hi {
		return Field{Raw: raw, Trimmed: Value{Span: source.Span{Start: raw.Span.Start, End: raw.Span.Start}}}
	}
	return Field{Raw: raw, Trimmed: s.v.value(from+lo, from+hi)}
}
