package gantt

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
	modeClick
	modeHref
	modeCallName
	modeCallArgs
)

type scanner struct {
	text      string
	start     []int
	end       []int
	length    int
	at        int
	mode      mode
	open      source.Span
	delim     int
	keyword   int
	clickRead bool
	crossed   bool
	pending   *Token
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
	start := make([]int, 0, len(kept)+2)
	end := make([]int, 0, len(kept)+2)
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

func lineLen(text string) int {
	if i := strings.IndexByte(text, '\n'); i >= 0 {
		return i
	}
	return len(text)
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
	return Token{Kind: kind, Text: s.text[from:to], Span: s.span(from, to)}
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
		return s.value(KindAccTitleValue)
	case modeAccDescr:
		return s.value(KindAccDescrValue)
	case modeBlock:
		return s.block()
	case modeClick:
		return s.click()
	case modeHref:
		return s.href()
	case modeCallName:
		return s.callName()
	case modeCallArgs:
		return s.callArgs()
	}
	return s.initial()
}

func (s *scanner) unterminated(text string, at int) (Token, bool) {
	s.mode = modeInitial
	s.at = len(s.text)
	return Token{Kind: kindOpen, Text: text, Span: source.Span{Start: s.start[at], End: s.length}}, true
}

func (s *scanner) finish() (Token, bool) {
	switch s.mode {
	case modeBlock:
		return s.unterminated("{", s.delim)
	case modeHref:
		return s.unterminated("\"", s.delim)
	case modeCallArgs:
		return s.unterminated("(", s.delim)
	case modeCallName:
		return s.unterminated("call", s.keyword)
	case modeClick:
		s.mode = modeInitial
		if !s.clickRead {
			zero := source.Span{Start: s.length, End: s.length}
			return Token{Kind: KindClick, Span: s.span(s.keyword, len(s.text)), Payload: zero}, true
		}
	}
	s.mode = modeInitial
	zero := source.Span{Start: s.length, End: s.length}
	return Token{Kind: KindEOF, Span: zero, Payload: zero}, true
}

func (s *scanner) value(kind string) (Token, bool) {
	at := s.at
	end := at + lineLen(s.text[at:])
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
	t := Token{Kind: KindAccBlockValue, Text: s.text[at:end], Value: s.text[at:end], Span: s.span(at, end)}
	t.Payload = t.Span
	t.Open = s.open
	t.Close = s.span(end, end+1)
	return t, true
}

func (s *scanner) click() (Token, bool) {
	r, n := s.rune(s.at)
	if IsSpace(r) {
		s.mode = modeInitial
		return s.skip(s.at + n)
	}
	end := s.at
	for end < len(s.text) {
		c, w := s.rune(end)
		if IsSpace(c) {
			break
		}
		end += w
	}
	s.clickRead = true
	return s.payloadToken(KindClick, s.keyword, s.at, end), true
}

func (s *scanner) href() (Token, bool) {
	at := s.at
	if s.text[at] == '"' {
		s.mode = modeInitial
		return s.skip(at + 1)
	}
	rel := strings.IndexByte(s.text[at:], '"')
	if rel < 0 {
		return s.finish()
	}
	end := at + rel
	s.mode = modeInitial
	t := s.payloadToken(KindHref, s.keyword, at, end)
	t.Span = s.span(s.keyword, end+1)
	s.at = end + 1
	return t, true
}

func (s *scanner) emptyArgsEnd(at int) (int, bool) {
	if at >= len(s.text) || s.text[at] != '(' {
		return 0, false
	}
	ws := s.spaceRun(at + 1)
	if ws < len(s.text) && s.text[ws] == ')' {
		return ws + 1, true
	}
	return 0, false
}

func (s *scanner) callName() (Token, bool) {
	at := s.at
	if end, ok := s.emptyArgsEnd(at); ok {
		s.mode = modeInitial
		return s.skip(end)
	}
	if s.text[at] == '(' {
		s.delim = at
		s.mode = modeCallArgs
		s.at = at + 1
		return Token{}, false
	}
	rel := strings.IndexByte(s.text[at:], '(')
	if rel < 0 {
		return s.finish()
	}
	end := at + rel
	t := s.payloadToken(KindCallbackName, s.keyword, at, end)
	if closed, ok := s.emptyArgsEnd(end); ok {
		t.Span = s.span(s.keyword, closed)
		s.at = closed
		s.mode = modeInitial
	}
	return t, true
}

func (s *scanner) callArgs() (Token, bool) {
	at := s.at
	if s.text[at] == ')' {
		s.mode = modeInitial
		return s.skip(at + 1)
	}
	rel := strings.IndexByte(s.text[at:], ')')
	if rel < 0 {
		return s.finish()
	}
	end := at + rel
	s.mode = modeInitial
	t := s.payloadToken(KindCallbackArgs, s.delim, at, end)
	t.Span = s.span(s.delim, end+1)
	s.at = end + 1
	return t, true
}

func (s *scanner) newlineRun(from int) int {
	end := from
	for end < len(s.text) && s.text[end] == '\n' {
		end++
	}
	return end
}

func (s *scanner) trivia(at int) (t Token, emit, handled bool) {
	rest := s.text[at:]
	r, n := s.rune(at)
	switch {
	case strings.HasPrefix(rest, "%%"):
		t, emit = s.skip(at + lineLen(rest))
	case r != '}' && n < len(rest) && rest[n] == '%':
		t, emit = s.skip(at + n + lineLen(rest[n:]))
	case rest[0] == '%':
		t, emit = s.skip(s.newlineRun(at + lineLen(rest)))
	case rest[0] == '\n':
		t, emit = s.token(KindNewline, at, s.newlineRun(at)), true
	case IsSpace(r):
		t, emit = s.skip(s.spaceRun(at))
	default:
		return Token{}, false, false
	}
	return t, emit, true
}

func (s *scanner) initial() (Token, bool) {
	at := s.at
	if t, emit, handled := s.accessibility(at); handled {
		return t, emit
	}
	if t, emit, handled := s.trivia(at); handled {
		return t, emit
	}
	return s.statement(at)
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
			return s.token(KindAccTitle, at, after), true, true
		}
		s.mode = modeAccDescr
		return s.token(KindAccDescr, at, after), true, true
	}
	if descr && colon < len(s.text) && s.text[colon] == '{' {
		after := s.spaceRun(colon + 1)
		s.open = s.span(at, after)
		s.delim = colon
		s.mode = modeBlock
		s.at = after
		return Token{}, false, true
	}
	return Token{}, false, false
}

func (s *scanner) wordThenSpace(at int, word string) (int, bool) {
	if !s.fold(at, word) {
		return 0, false
	}
	after := at + len(word)
	run := s.spaceRun(after)
	return run, run > after
}

func (s *scanner) statement(at int) (Token, bool) {
	if run, ok := s.wordThenSpace(at, "href"); ok && run < len(s.text) && s.text[run] == '"' {
		s.keyword, s.delim, s.mode, s.at = at, run, modeHref, run+1
		return Token{}, false
	}
	if run, ok := s.wordThenSpace(at, "call"); ok {
		s.keyword, s.mode, s.at = at, modeCallName, run
		return Token{}, false
	}
	if run, ok := s.wordThenSpace(at, "click"); ok {
		s.keyword, s.mode, s.at, s.clickRead = at, modeClick, run, false
		return Token{}, false
	}
	return s.keywordToken(at)
}

func stopLine(c byte) bool { return c == '\n' }

func stopHashLine(c byte) bool { return c == '#' || c == '\n' || c == ';' }

func stopLineSemi(c byte) bool { return c == '\n' || c == ';' }

type payloadRule struct {
	word string
	kind string
	stop func(byte) bool
}

var payloadRules = [...]payloadRule{
	{"dateformat", KindDateFormat, stopHashLine},
	{"axisformat", KindAxisFormat, stopHashLine},
	{"tickinterval", KindTickInterval, stopHashLine},
	{"includes", KindIncludes, stopHashLine},
	{"excludes", KindExcludes, stopHashLine},
	{"todaymarker", KindTodayMarker, stopLineSemi},
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

func (s *scanner) keywordToken(at int) (Token, bool) {
	if s.fold(at, "gantt") {
		return s.token(KindGantt, at, at+len("gantt")), true
	}
	for _, rule := range payloadRules[:] {
		if from, end, ok := s.keywordPayload(at, rule.word, rule.stop); ok {
			return s.payloadToken(rule.kind, at, from, end), true
		}
	}
	for _, flag := range [...]struct{ word, kind string }{{"inclusiveenddates", KindInclusiveEndDates}, {"topaxis", KindTopAxis}} {
		if s.fold(at, flag.word) {
			return s.token(flag.kind, at, at+len(flag.word)), true
		}
	}
	if kind, end, ok := s.dayRule(at); ok {
		return s.token(kind, at, end), true
	}
	return s.lineRules(at)
}

func (s *scanner) dayRule(at int) (string, int, bool) {
	for _, group := range [...]struct {
		word, prefix string
		names        []string
	}{{"weekday", KindWeekdayPrefix, weekdays[:]}, {"weekend", KindWeekendPrefix, weekends[:]}} {
		run, ok := s.wordThenSpace(at, group.word)
		if !ok {
			continue
		}
		for _, name := range group.names {
			if s.fold(run, name) {
				return group.prefix + name, run + len(name), true
			}
		}
	}
	return "", 0, false
}

func (s *scanner) dateAt(at int) bool {
	const shape = "dddd-dd-dd"
	if at+len(shape) > len(s.text) {
		return false
	}
	for i := range len(shape) {
		c := s.text[at+i]
		if shape[i] == '-' && c != '-' || shape[i] == 'd' && (c < '0' || c > '9') {
			return false
		}
	}
	return true
}

func (s *scanner) lineRules(at int) (Token, bool) {
	if s.dateAt(at) {
		return s.token(KindDate, at, at+len("dddd-dd-dd")), true
	}
	if from, end, ok := s.keywordPayload(at, "title", stopLine); ok {
		return s.payloadToken(KindTitle, at, from, end), true
	}
	if from, end, ok := s.keywordPayload(at, "accdescription", stopHashLine); ok {
		return s.payloadToken(KindAccDescription, at, from, end), true
	}
	if from, end, ok := s.keywordPayload(at, "section", stopLine); ok {
		return s.payloadToken(KindSection, at, from, end), true
	}
	end := at
	for end < len(s.text) && s.text[end] != ':' && s.text[end] != '\n' {
		end++
	}
	if end > at {
		return s.payloadToken(KindTaskText, at, at, end), true
	}
	return s.colon(at)
}

func (s *scanner) colon(at int) (Token, bool) {
	if s.text[at] != ':' {
		_, n := s.rune(at)
		return s.token(KindInvalid, at, at+n), true
	}
	end := at + 1
	for end < len(s.text) && !stopHashLine(s.text[end]) {
		end++
	}
	if end > at+1 {
		return s.payloadToken(KindTaskData, at, at, end), true
	}
	return s.token(KindColon, at, at+1), true
}

func (s *scanner) skipLine(contentEnd int) int {
	for {
		s.crossed = false
		t, ok := s.step()
		if ok {
			switch t.Kind {
			case KindEOF, kindOpen:
				s.pending = &t
				return contentEnd
			case KindNewline:
			default:
				contentEnd = max(contentEnd, t.Span.End)
			}
		}
		if s.crossed && s.mode == modeInitial {
			return contentEnd
		}
	}
}
