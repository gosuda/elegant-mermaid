package timeline

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type mode uint8

const (
	modeInitial mode = iota
	modeAccTitle
	modeAccDescr
	modeBlock
)

type scanner struct {
	text    string
	start   []int
	end     []int
	length  int
	at      int
	mode    mode
	open    source.Span
	brace   int
	crossed bool
	pending *Token
}

func newScanner(src string, removed []source.Span) *scanner {
	skip := make([]bool, len(src))
	for _, span := range removed {
		for i := max(span.Start, 0); i < min(span.End, len(src)); i++ {
			skip[i] = true
		}
	}
	kept := make([]int, 0, len(src))
	for i := range len(src) {
		if !skip[i] {
			kept = append(kept, i)
		}
	}
	var text strings.Builder
	start := make([]int, 0, len(kept)+1)
	end := make([]int, 0, len(kept)+1)
	for k := 0; k < len(kept); k++ {
		i := kept[k]
		last := i
		c := src[i]
		if c == '\r' {
			if k+1 < len(kept) && src[kept[k+1]] == '\n' {
				k++
				last = kept[k]
			}
			c = '\n'
		}
		text.WriteByte(c)
		start = append(start, i)
		end = append(end, last+1)
	}
	text.WriteByte('\n')
	start = append(start, len(src), len(src))
	end = append(end, len(src), len(src))
	return &scanner{text: text.String(), start: start, end: end, length: len(src)}
}

func IsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func (s *scanner) rune(at int) (rune, int) { return utf8.DecodeRuneInString(s.text[at:]) }

func (s *scanner) spaceRun(at int) int {
	for at < len(s.text) {
		r, n := s.rune(at)
		if !IsSpace(r) {
			break
		}
		at += n
	}
	return at
}

func (s *scanner) lineEnd(at int) int {
	if i := strings.IndexByte(s.text[at:], '\n'); i >= 0 {
		return at + i
	}
	return len(s.text)
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

func (s *scanner) span(from, to int) source.Span {
	if from >= to {
		at := s.start[min(from, len(s.text))]
		return source.Span{Start: at, End: at}
	}
	return source.Span{Start: s.start[from], End: s.end[to-1]}
}

func (s *scanner) token(kind string, from, to int) Token {
	s.at = to
	if strings.IndexByte(s.text[from:to], '\n') >= 0 {
		s.crossed = true
	}
	span := s.span(from, to)
	return Token{Kind: kind, Text: s.text[from:to], Span: span}
}

func (s *scanner) payloadToken(kind string, from, valueFrom, to int) Token {
	t := s.token(kind, from, to)
	t.Value = s.text[valueFrom:to]
	t.Payload = s.span(valueFrom, to)
	return t
}

func (s *scanner) skip(to int) (Token, bool) {
	if strings.IndexByte(s.text[s.at:to], '\n') >= 0 {
		s.crossed = true
	}
	s.at = to
	return Token{}, false
}

func (s *scanner) next() Token {
	if s.pending != nil {
		t := *s.pending
		s.pending = nil
		return t
	}
	for {
		if t, ok := s.step(); ok {
			return t
		}
	}
}

func (s *scanner) step() (Token, bool) {
	if s.at >= len(s.text) {
		return s.finish()
	}
	switch s.mode {
	case modeAccTitle:
		return s.value(kindAccTitleV)
	case modeAccDescr:
		return s.value(kindAccDescrV)
	case modeBlock:
		return s.block()
	}
	return s.initial()
}

func (s *scanner) finish() (Token, bool) {
	zero := source.Span{Start: s.length, End: s.length}
	if s.mode == modeBlock {
		s.mode = modeInitial
		s.at = len(s.text)
		return Token{Kind: kindOpen, Text: "{", Span: source.Span{Start: s.start[s.brace], End: s.length}}, true
	}
	s.mode = modeInitial
	return Token{Kind: kindEOF, Span: zero, Payload: zero}, true
}

func (s *scanner) value(kind string) (Token, bool) {
	at := s.at
	end := s.lineEnd(at)
	s.mode = modeInitial
	t := s.token(kind, at, end)
	t.Value = t.Text
	t.Payload = t.Span
	return t, true
}

func (s *scanner) block() (Token, bool) {
	at := s.at
	rel := strings.IndexByte(s.text[at:], '}')
	if rel < 0 {
		return s.finish()
	}
	end := at + rel
	s.mode = modeInitial
	s.at = end + 1
	if rel == 0 {
		return Token{}, false
	}
	t := Token{Kind: kindAccBlockV, Text: s.text[at:end], Value: s.text[at:end], Span: s.span(at, end)}
	t.Payload = t.Span
	t.Open = s.open
	t.Close = s.span(end, end+1)
	return t, true
}

func lineLen(text string) int {
	if i := strings.IndexByte(text, '\n'); i >= 0 {
		return i
	}
	return len(text)
}

func (s *scanner) initial() (Token, bool) {
	if s.trivia() {
		return Token{}, false
	}
	at := s.at
	if s.text[at] == '\n' {
		end := at
		for end < len(s.text) && s.text[end] == '\n' {
			end++
		}
		return s.token(kindNewline, at, end), true
	}
	if t, ok := s.header(at); ok {
		return t, true
	}
	return s.statement(at)
}

func (s *scanner) trivia() bool {
	at := s.at
	rest := s.text[at:]
	var to int
	switch r, n := s.rune(at); {
	case strings.HasPrefix(rest, "%%") && !strings.HasPrefix(rest, "%%{"):
		to = at + lineLen(rest)
	case r != '}' && strings.HasPrefix(rest[n:], "%%"):
		to = at + n + 2 + lineLen(rest[n+2:])
	case rest[0] == '\n':
		return false
	case s.spaceRun(at) > at:
		to = s.spaceRun(at)
	case rest[0] == '#' && s.entityLen(at) == 0:
		to = at + lineLen(rest)
	default:
		return false
	}
	s.skip(to)
	return true
}

func (s *scanner) boundary(at int) bool {
	return at >= len(s.text) || !wordByte(s.text[at])
}

func wordByte(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func (s *scanner) header(at int) (Token, bool) {
	if !s.fold(at, "timeline") {
		return Token{}, false
	}
	word := at + len("timeline")
	gap := word
	for gap < len(s.text) && (s.text[gap] == ' ' || s.text[gap] == '\t') {
		gap++
	}
	if gap > word && s.boundary(gap+2) {
		if s.fold(gap, "lr") {
			return s.token(kindTimelineLR, at, gap+2), true
		}
		if s.fold(gap, "td") {
			return s.token(kindTimelineTD, at, gap+2), true
		}
	}
	if !s.boundary(word) {
		return Token{}, false
	}
	return s.token(kindTimeline, at, word), true
}

func (s *scanner) keywordPayload(at int, word string, stop func(byte) bool) (int, int, bool) {
	if !s.fold(at, word) {
		return 0, 0, false
	}
	gap := at + len(word)
	if gap >= len(s.text) {
		return 0, 0, false
	}
	r, n := s.rune(gap)
	if !IsSpace(r) {
		return 0, 0, false
	}
	from := gap + n
	end := from
	for end < len(s.text) && !stop(s.text[end]) {
		end++
	}
	return from, end, end > from
}

func (s *scanner) statement(at int) (Token, bool) {
	if from, end, ok := s.keywordPayload(at, "title", func(c byte) bool { return c == '\n' }); ok {
		return s.payloadToken(kindTitle, at, from, end), true
	}
	if t, emit, handled := s.accessibility(at); handled {
		return t, emit
	}
	if from, end, ok := s.keywordPayload(at, "section", func(c byte) bool { return c == '\n' || c == ':' }); ok {
		return s.payloadToken(kindSection, at, from, end), true
	}
	if from, end, ok := s.event(at); ok {
		return s.payloadToken(kindEvent, at, from, end), true
	}
	if end := s.periodEnd(at); end > at {
		return s.payloadToken(kindPeriod, at, at, end), true
	}
	_, n := s.rune(at)
	return s.token(kindInvalid, at, at+n), true
}

func (s *scanner) accessibility(at int) (t Token, emit, handled bool) {
	title, descr := s.fold(at, "acctitle"), s.fold(at, "accdescr")
	if !title && !descr {
		return Token{}, false, false
	}
	word := at + len("acctitle")
	colon := s.spaceRun(word)
	if colon < len(s.text) && s.text[colon] == ':' {
		after := s.spaceRun(colon + 1)
		if title {
			s.mode = modeAccTitle
			return s.token(kindAccTitle, at, after), true, true
		}
		s.mode = modeAccDescr
		return s.token(kindAccDescr, at, after), true, true
	}
	if descr && colon < len(s.text) && s.text[colon] == '{' {
		after := s.spaceRun(colon + 1)
		s.open = s.span(at, after)
		s.brace = colon
		s.mode = modeBlock
		s.at = after
		return Token{}, false, true
	}
	return Token{}, false, false
}

func (s *scanner) event(at int) (int, int, bool) {
	if s.text[at] != ':' || at+1 >= len(s.text) {
		return 0, 0, false
	}
	r, n := s.rune(at + 1)
	if !IsSpace(r) {
		return 0, 0, false
	}
	from := at + 1 + n
	end := from
	for end < len(s.text) {
		c := s.text[end]
		if c == '\n' {
			break
		}
		if c == ':' && end+1 < len(s.text) {
			if next, _ := s.rune(end + 1); IsSpace(next) {
				break
			}
		}
		_, w := s.rune(end)
		end += w
	}
	return from, end, end > from
}

func (s *scanner) entityLen(at int) int {
	end := at + 1
	for end < len(s.text) && wordByte(s.text[end]) {
		end++
	}
	if end == at+1 || end >= len(s.text) || s.text[end] != ';' {
		return 0
	}
	return end + 1 - at
}

func (s *scanner) periodEnd(at int) int {
	end := at
	for end < len(s.text) {
		c := s.text[end]
		if c == '#' {
			n := s.entityLen(end)
			if n == 0 {
				break
			}
			end += n
			continue
		}
		if c == ':' || c == '\n' {
			break
		}
		end++
	}
	return end
}

func (s *scanner) skipLine(contentEnd int) int {
	for {
		s.crossed = false
		t, ok := s.step()
		if ok {
			switch t.Kind {
			case kindEOF, kindOpen:
				s.pending = &t
				return contentEnd
			case kindNewline:
			default:
				contentEnd = max(contentEnd, t.Span.End)
			}
		}
		if s.crossed && s.mode == modeInitial {
			return contentEnd
		}
	}
}
