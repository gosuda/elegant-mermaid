package wardley

import (
	"slices"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var keywords = []struct{ text, kind string }{
	{"wardley-beta", "KW_WARDLEY"}, {"size", "KW_SIZE"}, {"evolution", "KW_EVOLUTION"}, {"anchor", "KW_ANCHOR"},
	{"component", "KW_COMPONENT"}, {"label", "KW_LABEL"}, {"inertia", "KW_INERTIA"}, {"evolve", "KW_EVOLVE"},
	{"pipeline", "KW_PIPELINE"}, {"note", "KW_NOTE"}, {"annotations", "KW_ANNOTATIONS"}, {"annotation", "KW_ANNOTATION"},
	{"accelerator", "KW_ACCELERATOR"}, {"deaccelerator", "KW_DEACCELERATOR"},
}

var (
	strategies  = []string{"build", "buy", "outsource", "market"}
	linkPorts   = []string{"+<>", "+>", "+<"}
	linkArrows  = []string{"-->", "-.->", ">"}
	quotedFlows = []string{"<>", "<", ">"}
)

const punctuation = "[,]@/-(){}"

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
		if !s.hidden() && !s.next() {
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

func (s *scanner) hidden() bool {
	if n := horizontalRun(s.src[s.at:]); n > 0 {
		s.at += n
		return true
	}
	if strings.HasPrefix(s.src[s.at:], "%%") {
		s.at += lineLength(s.src[s.at:])
		return true
	}
	return false
}

var scanRules = []func(*scanner) bool{
	(*scanner).newline, (*scanner).punctuation, (*scanner).number, (*scanner).linkPort, (*scanner).linkArrow,
	(*scanner).linkLabel, (*scanner).strategy, (*scanner).keyword, (*scanner).name, (*scanner).metadata,
	(*scanner).integer, (*scanner).stringLiteral, (*scanner).identifier,
}

func (s *scanner) next() bool {
	return slices.ContainsFunc(scanRules, func(rule func(*scanner) bool) bool { return rule(s) })
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

func (s *scanner) unterminated(opener int, text string) {
	end := len(s.src)
	s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: text, Span: source.Span{Start: opener, End: end}})
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

func isLetter(c byte) bool { return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' }

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func isWord(c byte) bool { return isLetter(c) || isDigit(c) || c == '_' }

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func (s *scanner) punctuation() bool {
	c := s.src[s.at]
	if strings.IndexByte(punctuation, c) < 0 {
		return false
	}
	if c == '-' {
		rest := s.src[s.at:]
		switch {
		case strings.HasPrefix(rest, "->"):
			s.emit("ARROW", 2)
			return true
		case strings.HasPrefix(rest, "-->"):
			s.emit("LINK_ARROW", 3)
			return true
		case strings.HasPrefix(rest, "-.->"):
			s.emit("LINK_ARROW", 4)
			return true
		}
	}
	s.emit(string(c), 1)
	return true
}

func (s *scanner) number() bool {
	rest := s.src[s.at:]
	whole := 0
	for whole < len(rest) && isDigit(rest[whole]) {
		whole++
	}
	if whole == 0 || whole >= len(rest) || rest[whole] != '.' {
		return false
	}
	fraction := 0
	for whole+1+fraction < len(rest) && isDigit(rest[whole+1+fraction]) {
		fraction++
	}
	if fraction == 0 {
		return false
	}
	s.emit("WARDLEY_NUMBER", whole+1+fraction)
	return true
}

func (s *scanner) linkPort() bool {
	rest := s.src[s.at:]
	for _, port := range linkPorts {
		if strings.HasPrefix(rest, port) {
			s.emit("LINK_PORT", len(port))
			return true
		}
	}
	return false
}

func (s *scanner) linkArrow() bool {
	rest := s.src[s.at:]
	for _, arrow := range linkArrows {
		if strings.HasPrefix(rest, arrow) {
			s.emit("LINK_ARROW", len(arrow))
			return true
		}
	}
	if !strings.HasPrefix(rest, "+'") {
		return false
	}
	closing := strings.IndexByte(rest[2:], '\'')
	if closing < 0 {
		return false
	}
	head := 2 + closing + 1
	for _, flow := range quotedFlows {
		if strings.HasPrefix(rest[head:], flow) {
			s.emit("LINK_ARROW", head+len(flow))
			return true
		}
	}
	return false
}

func (s *scanner) linkLabel() bool {
	rest := s.src[s.at:]
	if rest[0] != ';' {
		return false
	}
	n := lineLength(rest[1:])
	if n == 0 {
		return false
	}
	s.emitValue("LINK_LABEL", 1+n, strings.TrimFunc(rest[1:1+n], jsSpace))
	return true
}

func (s *scanner) strategy() bool {
	rest := s.src[s.at:]
	for _, strategy := range strategies {
		if strings.HasPrefix(rest, strategy) {
			s.emit("STRATEGY", len(strategy))
			return true
		}
	}
	return false
}

func (s *scanner) headerPosition() bool {
	for _, t := range s.tokens {
		if t.Kind != "NEWLINE" {
			return false
		}
	}
	return true
}

func (s *scanner) keyword() bool {
	rest := s.src[s.at:]
	if s.headerPosition() && foldPrefix(rest, "wardley-beta") {
		s.emit("KW_WARDLEY", len("wardley-beta"))
		return true
	}
	for _, k := range keywords {
		if strings.HasPrefix(rest, k.text) {
			s.emit(k.kind, len(k.text))
			return true
		}
	}
	return false
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

func isNameByte(c byte) bool { return isWord(c) || c == '(' || c == ')' || c == '&' }

func nameRun(text string, from int) int {
	i := from
	for i < len(text) {
		c := text[i]
		switch {
		case isNameByte(c):
			i++
		case c == '-' && (i+1 >= len(text) || text[i+1] != '>'):
			i++
		default:
			return i
		}
	}
	return i
}

func excludedName(text string) bool {
	if strings.HasPrefix(text, "accTitle") || strings.HasPrefix(text, "accDescr") {
		return true
	}
	if !strings.HasPrefix(text, "title") || len(text) == len("title") {
		return false
	}
	r, _ := utf8.DecodeRuneInString(text[len("title"):])
	return jsSpace(r)
}

func nameLength(text string) int {
	if text == "" || !isLetter(text[0]) || excludedName(text) {
		return 0
	}
	n := nameRun(text, 1)
	for {
		blanks := horizontalRun(text[n:])
		next := n + blanks
		if blanks == 0 || next >= len(text) || !isLetter(text[next]) && text[next] != '(' {
			return n
		}
		n = nameRun(text, next+1)
	}
}

func (s *scanner) name() bool {
	n := nameLength(s.src[s.at:])
	if n == 0 {
		return false
	}
	s.emit("NAME_WITH_SPACES", n)
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
		if after == "" || !horizontal(after[0]) {
			s.emitValue("TITLE", len("title"), "")
			return true
		}
		return s.line("TITLE", len("title"), after)
	}
	return false
}

func commentCut(line string) int {
	if i := strings.Index(line, "%%"); i >= 0 {
		return i
	}
	return len(line)
}

func (s *scanner) line(kind string, prefix int, value string) bool {
	value = value[:lineLength(value)]
	value = value[:commentCut(value)]
	s.emitValue(kind, prefix+len(value), collapseLine(value))
	return true
}

func (s *scanner) accDescr(after string) bool {
	if colon := horizontalRun(after); colon < len(after) && after[colon] == ':' {
		return s.line("ACC_DESCR", len("accDescr")+colon+1, after[colon+1:])
	}
	space := 0
	for space < len(after) {
		r, size := utf8.DecodeRuneInString(after[space:])
		if !jsSpace(r) {
			break
		}
		space += size
	}
	if space >= len(after) || after[space] != '{' {
		return false
	}
	body := after[space+1:]
	closing := strings.IndexByte(body, '}')
	if closing < 0 {
		s.unterminated(s.at+len("accDescr")+space, "{")
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
	digits := 1
	for digits < len(text) && isDigit(text[digits]) {
		digits++
	}
	if digits < len(text) && text[digits] == '.' {
		digits--
	}
	return digits
}

func (s *scanner) integer() bool {
	n := integerLength(s.src[s.at:])
	if n == 0 {
		return false
	}
	s.emit("INT", n)
	return true
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
		r, size := utf8.DecodeRuneInString(s.src[i:])
		if c != '\\' {
			value.WriteRune(r)
			i += size
			continue
		}
		if i+1 >= len(s.src) {
			break
		}
		escape, width := utf8.DecodeRuneInString(s.src[i+1:])
		if lineTerminator(escape) {
			break
		}
		value.WriteString(escaped(escape))
		i += 1 + width
	}
	s.unterminated(s.at, string(quote))
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

func (s *scanner) identifier() bool {
	rest := s.src[s.at:]
	if !isWord(rest[0]) {
		return false
	}
	n := 1
	for n < len(rest) && (isWord(rest[n]) || rest[n] == '-') {
		n++
	}
	for n > 1 && rest[n-1] == '-' {
		n--
	}
	s.emit("ID", n)
	return true
}
