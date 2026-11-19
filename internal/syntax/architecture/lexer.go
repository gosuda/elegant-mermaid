package architecture

import (
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var keywords = []string{"architecture-beta", "architecture", "junction", "service", "column", "group", "align", "row", "in"}

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
	if s.newline() || s.keyword() || s.punctuation() || s.arrow() || s.metadata() {
		return true
	}
	return s.value()
}

func (s *scanner) value() bool {
	return s.stringLiteral() || s.identifier() || s.space() || s.comment() || s.icon() || s.title()
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

func isWord(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func identifierLength(text string) int {
	if text == "" || !isWord(text[0]) {
		return 0
	}
	run := 1
	for run < len(text) && (isWord(text[run]) || text[run] == '-') {
		run++
	}
	for run > 1 && !isWord(text[run-1]) {
		run--
	}
	return run
}

func (s *scanner) keyword() bool {
	rest := s.src[s.at:]
	for _, k := range keywords {
		if strings.HasPrefix(rest, k) && identifierLength(rest) <= len(k) {
			s.emit(k, len(k))
			return true
		}
	}
	return false
}

func (s *scanner) punctuation() bool {
	rest := s.src[s.at:]
	switch {
	case strings.HasPrefix(rest, "--"):
		s.emit("--", 2)
	case rest[0] == '-':
		s.emit("-", 1)
	case rest[0] == ':':
		s.emit(":", 1)
	default:
		return false
	}
	return true
}

func (s *scanner) arrow() bool {
	rest := s.src[s.at:]
	switch {
	case strings.ContainsRune("LRTB", rune(rest[0])):
		s.emit("ARROW_DIRECTION", 1)
	case strings.HasPrefix(rest, "{group}"):
		s.emit("ARROW_GROUP", len("{group}"))
	case rest[0] == '<' || rest[0] == '>':
		s.emit("ARROW_INTO", 1)
	default:
		return false
	}
	return true
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

func (s *scanner) identifier() bool {
	n := identifierLength(s.src[s.at:])
	if n == 0 {
		return false
	}
	s.emit("ID", n)
	return true
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

func lineTerminator(r rune) bool { return r == '\n' || r == '\r' || r == 0x2028 || r == 0x2029 }

func (s *scanner) stringLiteral() bool {
	quote := s.src[s.at]
	if quote != '"' && quote != '\'' {
		return false
	}
	value, length, state := quoted(s.src[s.at:])
	switch state {
	case quotedClosed:
		s.emitValue("STRING", length, value)
	case quotedOpen:
		s.unterminated(s.at, 1)
	default:
		s.emitRune("INVALID")
	}
	return true
}

type quotedState uint8

const (
	quotedClosed quotedState = iota
	quotedOpen
	quotedBroken
)

func quoted(text string) (string, int, quotedState) {
	quote := text[0]
	var value strings.Builder
	for i := 1; i < len(text); {
		switch c := text[i]; {
		case c == quote:
			return value.String(), i + 1, quotedClosed
		case c == '\\' && i+1 < len(text):
			r, size := utf8.DecodeRuneInString(text[i+1:])
			if lineTerminator(r) {
				return "", 0, quotedBroken
			}
			value.WriteString(escaped(r))
			i += 1 + size
		case c == '\\':
			return "", 0, quotedOpen
		default:
			r, size := utf8.DecodeRuneInString(text[i:])
			value.WriteRune(r)
			i += size
		}
	}
	return "", 0, quotedOpen
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

func iconByte(c byte) bool { return isWord(c) || c == '-' || c == ':' }

func (s *scanner) icon() bool {
	rest := s.src[s.at:]
	if rest[0] != '(' {
		return false
	}
	run := 1
	for run < len(rest) && iconByte(rest[run]) {
		run++
	}
	switch {
	case run > 1 && run < len(rest) && rest[run] == ')':
		s.emitValue("ARCH_ICON", run+1, rest[1:run])
	case run == len(rest):
		s.unterminated(s.at, 1)
	default:
		s.emitRune("INVALID")
	}
	return true
}

func (s *scanner) title() bool {
	rest := s.src[s.at:]
	if rest[0] != '[' {
		return false
	}
	if length := titleLength(rest); length > 0 {
		s.emitValue("ARCH_TITLE", length, titleValue(rest[1:length-1]))
		return true
	}
	if !strings.ContainsAny(rest[1:], "\n\r[]") {
		s.unterminated(s.at, 1)
		return true
	}
	s.emitRune("INVALID")
	return true
}

func titleLength(text string) int {
	if n := quotedTitleLength(text); n > 0 {
		return n
	}
	run := 1
	for run < len(text) && !strings.ContainsRune("[]\r\n", rune(text[run])) {
		run++
	}
	if run > 1 && run < len(text) && text[run] == ']' {
		return run + 1
	}
	return 0
}

func quotedTitleLength(text string) int {
	if len(text) <= 1 || text[1] != '"' && text[1] != '\'' {
		return 0
	}
	_, length, state := quoted(text[1:])
	if state == quotedClosed && 1+length < len(text) && text[1+length] == ']' {
		return length + 2
	}
	return 0
}

func titleValue(inner string) string {
	result := jsTrim(inner)
	if len(result) >= 1 && (result[0] == '"' || result[0] == '\'') && result[0] == result[len(result)-1] {
		if len(result) == 1 {
			result = ""
		} else {
			result = result[1 : len(result)-1]
		}
		result = strings.ReplaceAll(strings.ReplaceAll(result, `\"`, `"`), `\'`, `'`)
	}
	return jsTrim(result)
}

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0x00a0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func jsTrim(text string) string { return strings.TrimFunc(text, jsSpace) }
