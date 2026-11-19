package usecase

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	modeDefault    = "defaultMode"
	modeJSON       = "jsonBody"
	modeStereotype = "stereotype"
)

type scanner struct {
	src     string
	cleaned *source.Cleaned
	at      int
	mode    string
	tokens  []Token
}

func Lex(src string, removed []source.Span) []Token {
	return lex(source.Clean([]byte(src), removed))
}

func lex(cleaned *source.Cleaned) []Token {
	s := scanner{src: string(cleaned.Text), cleaned: cleaned, mode: modeDefault}
	for s.at < len(s.src) {
		s.next()
	}
	return s.tokens
}

func (s *scanner) emit(kind string, n int) {
	end := s.at + n
	s.tokens = append(s.tokens, Token{Kind: kind, Text: s.src[s.at:end], Span: s.cleaned.Span(s.at, end)})
	s.at = end
}

func (s *scanner) next() {
	rest := s.src[s.at:]
	switch s.mode {
	case modeJSON:
		s.json(rest)
		return
	case modeStereotype:
		s.stereotype(rest)
		return
	}
	if ws := countWhile(rest, func(b byte) bool { return b == ' ' || b == '\t' }); ws > 0 {
		s.at += ws
		return
	}
	if s.special(rest) || s.keyword(rest) || s.operator(rest) || s.atom(rest) {
		return
	}
	_, size := utf8.DecodeRuneInString(rest)
	s.emit("INVALID", size)
}

func (s *scanner) special(rest string) bool {
	switch {
	case strings.HasPrefix(rest, "\"`"):
		s.markdownString(rest)
		return true
	case strings.HasPrefix(rest, "%%") && s.lineStart():
		s.emit("COMMENT", lineLen(rest))
		return true
	case rest[0] == '\r' || rest[0] == '\n':
		n := 1
		if strings.HasPrefix(rest, "\r\n") {
			n = 2
		}
		s.emit("NEWLINE", n)
		return true
	case s.accessibility(rest):
		return true
	}
	if n, ok := jsonHeader(rest); ok {
		s.emit("JSON_DECLARATION_START", n)
		s.mode = modeJSON
		return true
	}
	return false
}

func (s *scanner) markdownString(rest string) {
	if i := strings.Index(rest[2:], "`\""); i >= 0 {
		s.emit("MARKDOWN_STRING", i+4)
		return
	}
	s.emit("UNCLOSED_MARKDOWN_STRING", len(rest))
}

func (s *scanner) lineStart() bool {
	for i := s.at - 1; i >= 0; i-- {
		switch s.src[i] {
		case '\r', '\n':
			return true
		case ' ', '\t':
		default:
			return false
		}
	}
	return true
}

func (s *scanner) accessibility(rest string) bool {
	if !s.lineStart() {
		return false
	}
	for _, name := range [...]struct{ text, kind string }{{"accTitle", "ACC_TITLE_LINE"}, {"accDescr", "ACC_DESCR_LINE"}} {
		tail, ok := strings.CutPrefix(rest, name.text)
		if !ok {
			continue
		}
		tail = strings.TrimLeft(tail, " \t")
		if strings.HasPrefix(tail, ":") {
			s.emit(name.kind, lineLen(rest))
			return true
		}
		if name.text == "accDescr" && strings.HasPrefix(tail, "{") {
			s.accessibilityBlock(rest, tail)
			return true
		}
	}
	return false
}

func (s *scanner) accessibilityBlock(rest, tail string) {
	if i := strings.IndexByte(tail, '}'); i >= 0 {
		s.emit("ACC_DESCR_BLOCK", len(rest)-len(tail)+i+1)
		return
	}
	s.emit("UNCLOSED_ACC_DESCR_BLOCK", len(rest))
}

func (s *scanner) keyword(rest string) bool {
	for _, k := range keywords {
		if len(rest) < len(k.text) {
			continue
		}
		prefix := rest[:len(k.text)]
		matches := prefix == k.text
		if k.kind == "INCLUDE" || k.kind == "EXTEND" {
			matches = equalASCIIFold(prefix, k.text)
		}
		if matches && wordLen(rest) <= len(k.text) {
			s.emit(k.kind, len(k.text))
			return true
		}
	}
	return false
}

func equalASCIIFold(a, b string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range len(a) {
		if lowerASCII(a[i]) != lowerASCII(b[i]) {
			return false
		}
	}
	return true
}

func lowerASCII(b byte) byte {
	if 'A' <= b && b <= 'Z' {
		return b + 'a' - 'A'
	}
	return b
}

func (s *scanner) operator(rest string) bool {
	for _, o := range operators {
		if strings.HasPrefix(rest, o.text) {
			s.emit(o.kind, len(o.text))
			if o.kind == "STEREOTYPE_START" {
				s.mode = modeStereotype
			}
			return true
		}
	}
	if s.solidArrow(rest) {
		return true
	}
	for _, o := range markedAssociations {
		if strings.HasPrefix(rest, o.text) {
			s.emit(o.kind, 3)
			return true
		}
	}
	if n := countWhile(rest, isDash); n >= 2 {
		s.emit("MARKERLESS_SOLID", n)
		return true
	}
	return false
}

func (s *scanner) solidArrow(rest string) bool {
	n := countWhile(rest, isDash)
	if n >= 2 && strings.HasPrefix(rest[n:], ">") {
		s.emit("FORWARD_SOLID", n+1)
		return true
	}
	if !strings.HasPrefix(rest, "<--") {
		return false
	}
	s.emit("BACKWARD_SOLID", countWhile(rest[1:], isDash)+1)
	return true
}

func (s *scanner) atom(rest string) bool {
	if s.delimiter(rest) {
		return true
	}
	if hex := countWhile(rest[1:], isHexDigit); rest[0] == '#' && hex > 0 {
		s.emit("HASH_COLOR", hex+1)
		return true
	}
	if rest[0] == '\'' || rest[0] == '"' {
		s.plainString(rest)
		return true
	}
	if css := cssLen(rest); css > 0 {
		s.emit("CSS_IDENTIFIER", css)
		return true
	}
	if s.identifier(rest) {
		return true
	}
	return s.punctuation(rest)
}

func (s *scanner) delimiter(rest string) bool {
	for _, d := range delimiters {
		if strings.HasPrefix(rest, d.text) {
			s.emit(d.kind, len(d.text))
			return true
		}
	}
	return false
}

func (s *scanner) identifier(rest string) bool {
	word, number := wordLen(rest), numberLen(rest)
	if word == 0 && number == 0 {
		return false
	}
	kind := "IDENTIFIER"
	if number > word {
		kind = "NUMBER"
	}
	s.emit(kind, max(word, number))
	return true
}

func (s *scanner) plainString(rest string) {
	line := lineLen(rest)
	if i := strings.IndexByte(rest[1:line], rest[0]); i >= 0 {
		s.emit("PLAIN_STRING", i+2)
		return
	}
	s.emit("UNCLOSED_PLAIN_STRING", line)
}

func (s *scanner) punctuation(rest string) bool {
	for _, p := range punctuations {
		if strings.HasPrefix(rest, p.text) {
			s.emit(p.kind, len(p.text))
			return true
		}
	}
	if kind := asciiPunctuation(rest[0]); kind != "" {
		s.emit(kind, 1)
		return true
	}
	if n := symbolLen(rest); n > 0 {
		s.emit("LABEL_SYMBOL", n)
		return true
	}
	return false
}

func asciiPunctuation(b byte) string {
	switch {
	case strings.IndexByte("!#$&*+/=?^_|~", b) >= 0:
		return "CSS_PUNCTUATION"
	case strings.IndexByte(";<>\\`", b) >= 0:
		return "LABEL_PUNCTUATION"
	}
	return ""
}

func symbolLen(s string) int {
	n := 0
	for n < len(s) {
		r, size := utf8.DecodeRuneInString(s[n:])
		if isPrintableOrLineSpace(r) {
			break
		}
		n += size
	}
	return n
}

func isPrintableOrLineSpace(r rune) bool {
	return r == '\t' || r == '\r' || r == '\n' || ' ' <= r && r <= '~'
}

func (s *scanner) stereotype(rest string) {
	if strings.HasPrefix(rest, ">>") {
		s.emit("STEREOTYPE_END", 2)
		s.mode = modeDefault
		return
	}
	line := lineLen(rest)
	if n := strings.Index(rest[:line], ">>"); n >= 0 && strings.TrimSpace(rest[:n]) != "" {
		s.emit("STEREOTYPE_TEXT", n)
		return
	}
	s.mode = modeDefault
	if line == 0 {
		s.next()
		return
	}
	s.emit("UNCLOSED_STEREOTYPE_TEXT", line)
}

func (s *scanner) json(rest string) {
	var balance jsonBalance
	for i := range len(rest) {
		if balance.advance(rest[i]) {
			s.emit("JSON_OBJECT_LITERAL", i+1)
			s.mode = modeDefault
			return
		}
	}
	s.emit("UNCLOSED_JSON_OBJECT_LITERAL", len(rest))
	s.mode = modeDefault
}

type jsonBalance struct {
	depth            int
	inString, escape bool
}

func (b *jsonBalance) advance(c byte) bool {
	switch {
	case b.escape:
		b.escape = false
	case b.inString:
		b.escape = c == '\\'
		b.inString = c != '"'
	default:
		return b.outside(c)
	}
	return false
}

func (b *jsonBalance) outside(c byte) bool {
	switch c {
	case '"':
		b.inString = true
	case '{':
		b.depth++
	case '}':
		b.depth = max(b.depth-1, 0)
		return b.depth == 0
	}
	return false
}

var keywords = [...]struct{ text, kind string }{
	{"usecase-beta", "USECASE"},
	{"actor", "ACTOR"},
	{"systemBoundary", "SYSTEM_BOUNDARY"},
	{"end", "END"},
	{"direction", "DIRECTION"},
	{"TD", "TD"},
	{"TB", "TB"},
	{"BT", "BT"},
	{"LR", "LR"},
	{"RL", "RL"},
	{"note", "NOTE"},
	{"for", "FOR"},
	{"json", "JSON"},
	{"classDef", "CLASS_DEF"},
	{"class", "CLASS"},
	{"style", "STYLE"},
	{"include", "INCLUDE"},
	{"extend", "EXTEND"},
	{"true", "TRUE"},
	{"false", "FALSE"},
}

var punctuations = [...]struct{ text, kind string }{
	{"\\,", "CSS_ESCAPED_COMMA"},
	{"-", "DASH"},
	{".", "DOT"},
	{"%", "PERCENT"},
}

var operators = [...]struct{ text, kind string }{
	{"--|>", "GENERALIZATION"},
	{"..>", "DEPENDENCY_ARROW"},
	{"<<", "STEREOTYPE_START"},
	{":::", "CLASS_SEPARATOR"},
}

var markedAssociations = [...]struct{ text, kind string }{
	{"--o", "FORWARD_CIRCLE"},
	{"o--", "BACKWARD_CIRCLE"},
	{"--x", "FORWARD_CROSS"},
	{"x--", "BACKWARD_CROSS"},
}

var delimiters = [...]struct{ text, kind string }{
	{"@{", "METADATA_START"},
	{"@", "AT"},
	{"{", "LBRACE"},
	{"}", "RBRACE"},
	{"[", "LBRACKET"},
	{"]", "RBRACKET"},
	{"(", "LPAREN"},
	{")", "RPAREN"},
	{",", "COMMA"},
	{":", "COLON"},
}

func isWord(kind string) bool {
	if kind == "IDENTIFIER" {
		return true
	}
	for _, k := range keywords {
		if k.kind == kind {
			return true
		}
	}
	return false
}

func isLabel(kind string) bool {
	if isWord(kind) {
		return true
	}
	switch kind {
	case "NUMBER", "AT", "COMMA", "COLON", "HASH_COLOR", "CSS_IDENTIFIER", "CSS_ESCAPED_COMMA", "DASH", "DOT", "PERCENT", "CSS_PUNCTUATION", "LABEL_PUNCTUATION", "LABEL_SYMBOL":
		return true
	}
	return false
}

func lineLen(s string) int {
	if i := strings.IndexAny(s, "\r\n"); i >= 0 {
		return i
	}
	return len(s)
}

func countWhile(s string, keep func(byte) bool) int {
	n := 0
	for n < len(s) && keep(s[n]) {
		n++
	}
	return n
}

func isDash(b byte) bool { return b == '-' }

func isDigit(b byte) bool { return '0' <= b && b <= '9' }

func isAlpha(b byte) bool { return 'a' <= b && b <= 'z' || 'A' <= b && b <= 'Z' }

func isWordByte(b byte) bool { return isAlpha(b) || isDigit(b) || b == '_' }

func isHexDigit(b byte) bool {
	return isDigit(b) || 'a' <= b && b <= 'f' || 'A' <= b && b <= 'F'
}

func wordLen(s string) int { return countWhile(s, isWordByte) }

func numberLen(s string) int {
	digits := countWhile(s, isDigit)
	n := digits
	if strings.HasPrefix(s[digits:], ".") {
		if fraction := countWhile(s[digits+1:], isDigit); fraction > 0 {
			n += 1 + fraction
		}
	}
	if n == 0 {
		return 0
	}
	return n + countWhile(s[n:], isAlpha)
}

func cssLen(s string) int {
	if s == "" || !isAlpha(s[0]) && s[0] != '_' {
		return 0
	}
	first := wordLen(s)
	n := first
	for strings.HasPrefix(s[n:], "-") {
		part := wordLen(s[n+1:])
		if part == 0 {
			break
		}
		n += 1 + part
	}
	if n > first {
		return n
	}
	return 0
}

func jsonHeader(s string) (int, bool) {
	tail, ok := strings.CutPrefix(s, "json")
	if !ok {
		return 0, false
	}
	t := strings.TrimLeft(tail, " \t")
	if len(t) == len(tail) {
		return 0, false
	}
	n := wordLen(t)
	if n == 0 {
		return 0, false
	}
	tail, ok = strings.CutPrefix(strings.TrimLeft(t[n:], " \t"), "@")
	if !ok {
		return 0, false
	}
	tail = strings.TrimLeft(tail, " \t")
	if !strings.HasPrefix(tail, "{") {
		return 0, false
	}
	return len(s) - len(tail), true
}
