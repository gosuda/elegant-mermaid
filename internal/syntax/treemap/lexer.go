package treemap

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
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
			s.emit("INVALID", utf8RuneLen(s.src[s.at:]))
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
	return s.directive() || s.structure() || s.operand()
}

func (s *scanner) directive() bool {
	return s.boolean() || s.metadata() || s.keyword() || s.classDef()
}

func (s *scanner) structure() bool {
	return s.separator() || s.indentation() || s.comment() || s.newline()
}

func (s *scanner) operand() bool {
	return s.identifier() || s.number() || s.quoted()
}

func utf8RuneLen(text string) int {
	_, size := utf8.DecodeRuneInString(text)
	return max(size, 1)
}

func (s *scanner) emit(kind string, length int) {
	end := min(s.at+length, len(s.src))
	s.tokens = append(s.tokens, Token{Kind: kind, Text: s.src[s.at:end], Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) emitValue(kind string, length int, text string) {
	end := min(s.at+length, len(s.src))
	s.tokens = append(s.tokens, Token{Kind: kind, Text: text, Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) unterminated(opener int) {
	s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: s.src[opener : opener+1], Span: source.Span{Start: opener, End: len(s.src)}})
	s.at = len(s.src)
}

func horizontal(c byte) bool { return c == ' ' || c == '\t' }

func horizontalRun(text string) int {
	n := 0
	for n < len(text) && horizontal(text[n]) {
		n++
	}
	return n
}

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func jsSpaceRun(text string) int {
	n := 0
	for n < len(text) {
		r, size := utf8.DecodeRuneInString(text[n:])
		if size == 0 || !jsSpace(r) {
			break
		}
		n += size
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

func (s *scanner) boolean() bool {
	rest := s.src[s.at:]
	switch {
	case strings.HasPrefix(rest, "true"):
		s.emit("BOOLEAN", len("true"))
	case strings.HasPrefix(rest, "false"):
		s.emit("BOOLEAN", len("false"))
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
	space := jsSpaceRun(after)
	if space >= len(after) || after[space] != '{' {
		return false
	}
	body := after[space+1:]
	closing := strings.IndexByte(body, '}')
	if closing < 0 {
		s.unterminated(s.at + lead + len("accDescr") + space)
		return true
	}
	s.emitValue("ACC_DESCR", lead+len("accDescr")+space+1+closing+1, collapseBlock(body[:closing]))
	return true
}

func jsTrim(value string) string {
	start, end := 0, len(value)
	for start < end {
		r, size := utf8.DecodeRuneInString(value[start:end])
		if !jsSpace(r) {
			break
		}
		start += size
	}
	for end > start {
		r, size := utf8.DecodeLastRuneInString(value[start:end])
		if !jsSpace(r) {
			break
		}
		end -= size
	}
	return value[start:end]
}

func collapseLine(value string) string {
	return collapseRuns(jsTrim(value))
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
		if trimmed := jsTrim(line); trimmed != "" {
			kept = append(kept, collapseRuns(trimmed))
		}
	}
	return strings.Join(kept, "\n")
}

func (s *scanner) keyword() bool {
	rest := s.src[s.at:]
	switch {
	case strings.HasPrefix(rest, "treemap-beta"):
		s.emit("TREEMAP_KEYWORD", len("treemap-beta"))
	case strings.HasPrefix(rest, "treemap"):
		s.emit("TREEMAP_KEYWORD", len("treemap"))
	default:
		return false
	}
	return true
}

func isWord(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func isNameStart(c byte) bool {
	return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func wordRun(text string) int {
	n := 0
	for n < len(text) && isWord(text[n]) {
		n++
	}
	return n
}

func classDefHead(rest string) (next int, name string, ok bool) {
	if !strings.HasPrefix(rest, "classDef") {
		return 0, "", false
	}
	n := len("classDef")
	space := jsSpaceRun(rest[n:])
	if space == 0 || n+space >= len(rest) || !isNameStart(rest[n+space]) {
		return 0, "", false
	}
	n += space
	run := wordRun(rest[n:])
	if run < 2 {
		return 0, "", false
	}
	return n + run, rest[n : n+run], true
}

func classDefStyle(rest string, from int) (style string, next int) {
	gap := jsSpaceRun(rest[from:])
	if gap == 0 {
		return "", from
	}
	begin := from + gap
	end := begin
	for end < len(rest) && rest[end] != ';' && rest[end] != '\r' && rest[end] != '\n' {
		end++
	}
	return rest[begin:end], end
}

func matchClassDef(rest string) (length int, name, style string, ok bool) {
	n, name, ok := classDefHead(rest)
	if !ok {
		return 0, "", "", false
	}
	style, n = classDefStyle(rest, n)
	if n < len(rest) && rest[n] == ';' {
		n++
	}
	return n, name, style, true
}

func (s *scanner) classDef() bool {
	n, _, _, ok := matchClassDef(s.src[s.at:])
	if !ok {
		return false
	}
	s.emit("CLASS_DEF", n)
	return true
}

func (s *scanner) separator() bool {
	rest := s.src[s.at:]
	switch {
	case strings.HasPrefix(rest, ":::"):
		s.emit("STYLE_SEPARATOR", 3)
	case strings.HasPrefix(rest, ":"):
		s.emit("SEPARATOR", 1)
	case strings.HasPrefix(rest, ","):
		s.emit("COMMA", 1)
	default:
		return false
	}
	return true
}

func (s *scanner) indentation() bool {
	n := horizontalRun(s.src[s.at:])
	if n == 0 {
		return false
	}
	s.emit("INDENTATION", n)
	return true
}

func (s *scanner) comment() bool {
	if !strings.HasPrefix(s.src[s.at:], "%%") {
		return false
	}
	s.at += lineLength(s.src[s.at:])
	return true
}

func (s *scanner) newline() bool {
	switch s.src[s.at] {
	case '\n':
		s.at++
	case '\r':
		s.at++
		if s.at < len(s.src) && s.src[s.at] == '\n' {
			s.at++
		}
	default:
		return false
	}
	return true
}

func (s *scanner) identifier() bool {
	if !isNameStart(s.src[s.at]) {
		return false
	}
	s.emit("ID2", wordRun(s.src[s.at:]))
	return true
}

func numberByte(c byte) bool {
	return c >= '0' && c <= '9' || c == '_' || c == '.' || c == ','
}

func startsNumber(c byte) bool { return c >= '0' && c <= '9' || c == '.' }

func (s *scanner) number() bool {
	if !startsNumber(s.src[s.at]) {
		return false
	}
	n := 1
	for s.at+n < len(s.src) && numberByte(s.src[s.at+n]) {
		n++
	}
	s.emit("NUMBER2", n)
	return true
}

func (s *scanner) quoted() bool {
	quote := s.src[s.at]
	if quote != '"' && quote != '\'' {
		return false
	}
	closing := strings.IndexByte(s.src[s.at+1:], quote)
	if closing < 0 {
		s.unterminated(s.at)
		return true
	}
	s.emit("STRING2", closing+2)
	return true
}
