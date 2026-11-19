package radar

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var keywords = []string{
	"radar-beta:", "radar-beta", "showLegend", "graticule", "curve", "ticks", "axis", "max", "min",
	",", ":", "[", "]", "{", "}",
}

const (
	headerKeyword = "radar-beta"
	anchorBefore  = "%%"
)

func lex(src string, removed []source.Span) []Token {
	s := &scanner{src: src, removed: removed}
	return s.run()
}

type scanner struct {
	src     string
	removed []source.Span
	at      int
	tokens  []Token
}

func (s *scanner) run() []Token {
	for s.at < len(s.src) {
		if end, ok := s.removedEnd(); ok {
			s.at = end
			continue
		}
		if !s.next() {
			s.emitRune("INVALID")
		}
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

var steps = []func(*scanner) bool{
	(*scanner).space, (*scanner).newline, (*scanner).keyword, (*scanner).graticule, (*scanner).boolean,
	(*scanner).metadata, (*scanner).number, (*scanner).stringLiteral, (*scanner).identifier, (*scanner).comment,
}

func (s *scanner) next() bool {
	for _, step := range steps {
		if step(s) {
			return true
		}
	}
	return false
}

func (s *scanner) emit(kind string, length int) {
	end := s.at + length
	s.tokens = append(s.tokens, Token{Kind: kind, Text: s.src[s.at:end], Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) emitValue(kind string, length int, text string) {
	end := s.at + length
	s.tokens = append(s.tokens, Token{Kind: kind, Text: text, Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) emitRune(kind string) {
	_, size := utf8.DecodeRuneInString(s.src[s.at:])
	s.emit(kind, size)
}

func (s *scanner) unterminated(opener, length int) {
	end := len(s.src)
	s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: s.src[opener : opener+length], Span: source.Span{Start: opener, End: end}})
	s.at = end
}

func horizontal(c byte) bool { return c == ' ' || c == '\t' }

func horizontalRun(text string) int {
	n := 0
	for n < len(text) && horizontal(text[n]) {
		n++
	}
	return n
}

func (s *scanner) space() bool {
	n := horizontalRun(s.src[s.at:])
	s.at += n
	return n > 0
}

func (s *scanner) newline() bool {
	switch s.src[s.at] {
	case '\n':
		s.emit("NEWLINE", 1)
	case '\r':
		n := 1
		if s.at+1 < len(s.src) && s.src[s.at+1] == '\n' {
			n = 2
		}
		s.emit("NEWLINE", n)
	default:
		return false
	}
	return true
}

func lineLength(text string) int {
	if i := strings.IndexAny(text, "\n\r"); i >= 0 {
		return i
	}
	return len(text)
}

func commentCut(line string) int {
	if i := strings.Index(line, anchorBefore); i >= 0 {
		return i
	}
	return len(line)
}

func isWord(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func isSpaceByte(c byte) bool {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' || c == '\f'
}

func idLength(text string) int {
	if text == "" || !isWord(text[0]) {
		return 0
	}
	run := 1
	for run < len(text) && (isWord(text[run]) || text[run] == '-') {
		run++
	}
	for text[run-1] == '-' {
		run--
	}
	return run
}

func digitRun(text string) int {
	n := 0
	for n < len(text) && isDigit(text[n]) {
		n++
	}
	return n
}

func floatLength(text string) int {
	whole := digitRun(text)
	if whole == 0 || whole >= len(text) || text[whole] != '.' {
		return 0
	}
	fraction := digitRun(text[whole+1:])
	if fraction == 0 {
		return 0
	}
	if end := whole + 1 + fraction; end < len(text) && text[end] == '.' {
		fraction--
		if fraction == 0 {
			return 0
		}
	}
	return whole + 1 + fraction
}

func integerLength(text string) int {
	if text == "" {
		return 0
	}
	if text[0] == '0' {
		return 1
	}
	if text[0] < '1' || text[0] > '9' {
		return 0
	}
	digits := digitRun(text)
	if digits < len(text) && text[digits] == '.' {
		digits--
	}
	return digits
}

func numberLength(text string) int {
	if n := floatLength(text); n > 0 {
		return n
	}
	return integerLength(text)
}

func headerGuard(after string) bool {
	if after == "" || strings.HasPrefix(after, anchorBefore) {
		return true
	}
	r, _ := utf8.DecodeRuneInString(after)
	return jsSpace(r)
}

func (s *scanner) keyword() bool {
	rest := s.src[s.at:]
	for _, k := range keywords {
		if !strings.HasPrefix(rest, k) {
			continue
		}
		if idLength(k) == len(k) && idLength(rest) > len(k) {
			continue
		}
		if k == headerKeyword && !headerGuard(rest[len(k):]) {
			continue
		}
		s.emit(k, len(k))
		return true
	}
	return false
}

func (s *scanner) literal(kind string, words []string) bool {
	rest := s.src[s.at:]
	for _, w := range words {
		if strings.HasPrefix(rest, w) {
			s.emit(kind, len(w))
			return true
		}
	}
	return false
}

func (s *scanner) graticule() bool { return s.literal("GRATICULE", []string{"circle", "polygon"}) }

func (s *scanner) boolean() bool { return s.literal("BOOLEAN", []string{"true", "false"}) }

func (s *scanner) number() bool {
	n := numberLength(s.src[s.at:])
	if n == 0 {
		return false
	}
	s.emit("NUMBER", n)
	return true
}

func (s *scanner) identifier() bool {
	n := idLength(s.src[s.at:])
	if n == 0 {
		return false
	}
	s.emit("ID", n)
	return true
}

func (s *scanner) comment() bool {
	if !strings.HasPrefix(s.src[s.at:], anchorBefore) {
		return false
	}
	s.at += lineLength(s.src[s.at:])
	return true
}

func (s *scanner) metadata() bool {
	rest := s.src[s.at:]
	switch {
	case strings.HasPrefix(rest, "accDescr"):
		return s.accDescr(rest[len("accDescr"):])
	case strings.HasPrefix(rest, "accTitle"):
		after := rest[len("accTitle"):]
		colon := horizontalRun(after)
		if colon >= len(after) || after[colon] != ':' {
			return false
		}
		return s.line("ACC_TITLE", len("accTitle")+colon+1, after[colon+1:])
	case strings.HasPrefix(rest, "title"):
		after := rest[len("title"):]
		if len(after) > 0 && horizontal(after[0]) {
			return s.line("TITLE", len("title"), after)
		}
		s.emitValue("TITLE", len("title"), "")
		return true
	}
	return false
}

func (s *scanner) line(kind string, prefix int, value string) bool {
	value = value[:commentCut(value[:lineLength(value)])]
	s.emitValue(kind, prefix+len(value), collapseLine(value))
	return true
}

func (s *scanner) accDescr(after string) bool {
	if colon := horizontalRun(after); colon < len(after) && after[colon] == ':' {
		return s.line("ACC_DESCR", len("accDescr")+colon+1, after[colon+1:])
	}
	space := 0
	for space < len(after) && isSpaceByte(after[space]) {
		space++
	}
	if space >= len(after) || after[space] != '{' {
		return false
	}
	body := after[space+1:]
	closing := strings.IndexByte(body, '}')
	if closing < 0 {
		s.unterminated(s.at+len("accDescr")+space, 1)
		return true
	}
	s.emitValue("ACC_DESCR", len("accDescr")+space+1+closing+1, collapseBlock(body[:closing]))
	return true
}

func collapseLine(value string) string {
	return collapseRuns(strings.TrimFunc(value, jsSpace))
}

func collapseRuns(value string) string {
	var b strings.Builder
	for i := 0; i < len(value); {
		if n := horizontalRun(value[i:]); n > 0 {
			if n == 1 {
				b.WriteByte(value[i])
			} else {
				b.WriteByte(' ')
			}
			i += n
			continue
		}
		b.WriteByte(value[i])
		i++
	}
	return b.String()
}

func collapseBlock(value string) string {
	var kept []string
	for _, line := range strings.FieldsFunc(value, func(r rune) bool { return r == '\n' || r == '\r' }) {
		if trimmed := strings.TrimFunc(line, jsSpace); trimmed != "" {
			kept = append(kept, collapseRuns(trimmed))
		}
	}
	return strings.Join(kept, "\n")
}

func escaped(r rune) string {
	switch r {
	case 'b':
		return "\b"
	case 'f':
		return "\f"
	case 'n':
		return "\n"
	case 'r':
		return "\r"
	case 't':
		return "\t"
	case 'v':
		return "\v"
	case '0':
		return "\x00"
	}
	return string(r)
}

func lineTerminator(r rune) bool { return r == '\n' || r == '\r' || r == 0x2028 || r == 0x2029 }

func (s *scanner) stringLiteral() bool {
	quote := s.src[s.at]
	if quote != '"' && quote != '\'' {
		return false
	}
	var value strings.Builder
	for i := s.at + 1; i < len(s.src); {
		c := s.src[i]
		if c == quote {
			s.emitValue("STRING", i+1-s.at, value.String())
			return true
		}
		if c != '\\' {
			r, size := utf8.DecodeRuneInString(s.src[i:])
			value.WriteRune(r)
			i += size
			continue
		}
		if i+1 >= len(s.src) {
			break
		}
		r, size := utf8.DecodeRuneInString(s.src[i+1:])
		if lineTerminator(r) {
			s.emitRune("INVALID")
			return true
		}
		value.WriteString(escaped(r))
		i += 1 + size
	}
	s.unterminated(s.at, 1)
	return true
}
