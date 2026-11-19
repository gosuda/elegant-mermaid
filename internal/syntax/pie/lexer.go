package pie

import (
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var keywords = []string{"showData", "pie", ":"}

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

func (s *scanner) next() bool {
	if s.newline() || s.metadata() || s.keyword() {
		return true
	}
	return s.number() || s.stringLiteral() || s.space() || s.comment() || s.word()
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

func horizontal(c byte) bool { return c == ' ' || c == '\t' }

func horizontalRun(text string) int {
	n := 0
	for n < len(text) && horizontal(text[n]) {
		n++
	}
	return n
}

func lineLength(text string) int {
	if i := strings.IndexAny(text, "\n\r"); i >= 0 {
		return i
	}
	return len(text)
}

func commentCut(line string) int {
	if i := strings.Index(line, "%%"); i >= 0 {
		return i
	}
	return len(line)
}

func (s *scanner) metadata() bool {
	lead := horizontalRun(s.src[s.at:])
	rest := s.src[s.at+lead:]
	switch {
	case strings.HasPrefix(rest, "accDescr"):
		return s.accDescr(lead, rest[len("accDescr"):])
	case strings.HasPrefix(rest, "accTitle"):
		after := rest[len("accTitle"):]
		colon := horizontalRun(after)
		if colon >= len(after) || after[colon] != ':' {
			return false
		}
		return s.line("ACC_TITLE", lead+len("accTitle")+colon+1, after[colon+1:])
	case strings.HasPrefix(rest, "title"):
		after := rest[len("title"):]
		if len(after) > 0 && horizontal(after[0]) {
			return s.line("TITLE", lead+len("title"), after)
		}
		s.emitValue("TITLE", lead+len("title"), "")
		return true
	}
	return false
}

func (s *scanner) line(kind string, prefix int, value string) bool {
	value = value[:commentCut(value[:lineLength(value)])]
	s.emitValue(kind, prefix+len(value), collapseLine(value))
	return true
}

func (s *scanner) accDescr(lead int, after string) bool {
	if colon := horizontalRun(after); colon < len(after) && after[colon] == ':' {
		return s.line("ACC_DESCR", lead+len("accDescr")+colon+1, after[colon+1:])
	}
	space := 0
	for space < len(after) && isSpace(after[space]) {
		space++
	}
	if space >= len(after) || after[space] != '{' {
		return false
	}
	body := after[space+1:]
	closing := strings.IndexByte(body, '}')
	if closing < 0 {
		s.unterminated(s.at+lead+len("accDescr")+space, 1)
		return true
	}
	s.emitValue("ACC_DESCR", lead+len("accDescr")+space+1+closing+1, collapseBlock(body[:closing]))
	return true
}

func isSpace(c byte) bool {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' || c == '\f'
}

func collapseLine(value string) string {
	return collapseRuns(strings.TrimFunc(value, unicode.IsSpace))
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
		if trimmed := strings.TrimFunc(line, unicode.IsSpace); trimmed != "" {
			kept = append(kept, collapseRuns(trimmed))
		}
	}
	return strings.Join(kept, "\n")
}

func (s *scanner) keyword() bool {
	rest := s.src[s.at:]
	for _, k := range keywords {
		if !strings.HasPrefix(rest, k) {
			continue
		}
		if idLength(rest) > len(k) {
			continue
		}
		s.emit(k, len(k))
		return true
	}
	return false
}

func isWord(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func idLength(text string) int {
	if text == "" || !isWord(text[0]) {
		return 0
	}
	run := 1
	for run < len(text) && (isWord(text[run]) || text[run] == '-') {
		run++
	}
	for run > 1 && text[run-1] == '-' {
		run--
	}
	return run
}

func (s *scanner) word() bool {
	n := idLength(s.src[s.at:])
	if n == 0 {
		return false
	}
	s.emit("ID", n)
	return true
}

func digitRun(text string) int {
	n := 0
	for n < len(text) && text[n] >= '0' && text[n] <= '9' {
		n++
	}
	return n
}

func notDot(text string, at int) bool { return at >= len(text) || text[at] != '.' }

func signLength(text string) int {
	if text != "" && text[0] == '-' {
		return 1
	}
	return 0
}

func floatLength(text string) int {
	sign := signLength(text)
	whole := digitRun(text[sign:])
	at := sign + whole
	if whole == 0 || at >= len(text) || text[at] != '.' {
		return 0
	}
	fraction := digitRun(text[at+1:])
	if fraction == 0 {
		return 0
	}
	end := at + 1 + fraction
	if notDot(text, end) {
		return end
	}
	if fraction == 1 {
		return 0
	}
	return end - 1
}

func integerLength(text string) int {
	sign := signLength(text)
	rest := text[sign:]
	switch {
	case rest == "":
		return 0
	case rest[0] == '0':
		if notDot(rest, 1) {
			return sign + 1
		}
		return 0
	case rest[0] < '1' || rest[0] > '9':
		return 0
	}
	digits := digitRun(rest)
	if notDot(rest, digits) {
		return sign + digits
	}
	if digits == 1 {
		return 0
	}
	return sign + digits - 1
}

func (s *scanner) number() bool {
	rest := s.src[s.at:]
	if n := floatLength(rest); n > 0 {
		s.emit("NUMBER_PIE", n)
		return true
	}
	if n := integerLength(rest); n > 0 {
		s.emit("NUMBER_PIE", n)
		return true
	}
	return false
}

func lineEndRune(r rune) bool { return r == '\n' || r == '\r' || r == 0x2028 || r == 0x2029 }

func (s *scanner) stringLiteral() bool {
	quote := s.src[s.at]
	if quote != '"' && quote != '\'' {
		return false
	}
	var value strings.Builder
	for i := s.at + 1; i < len(s.src); {
		c := s.src[i]
		switch {
		case c == quote:
			s.emitValue("STRING", i+1-s.at, value.String())
			return true
		case c == '\\' && i+1 < len(s.src):
			r, size := utf8.DecodeRuneInString(s.src[i+1:])
			if lineEndRune(r) {
				s.emit("INVALID", 1)
				return true
			}
			value.WriteString(escaped(r))
			i += 1 + size
		case c == '\\':
			s.unterminated(s.at, 1)
			return true
		default:
			r, size := utf8.DecodeRuneInString(s.src[i:])
			value.WriteRune(r)
			i += size
		}
	}
	s.unterminated(s.at, 1)
	return true
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

func (s *scanner) space() bool {
	n := horizontalRun(s.src[s.at:])
	s.at += n
	return n > 0
}

func (s *scanner) comment() bool {
	if !strings.HasPrefix(s.src[s.at:], "%%") {
		return false
	}
	s.at += lineLength(s.src[s.at:])
	return true
}
