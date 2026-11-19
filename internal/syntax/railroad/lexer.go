package railroad

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var headers = [...]string{"railroad-beta", "railroad-ebnf-beta", "railroad-abnf-beta", "railroad-peg-beta"}

var wordKeywords = []string{"nonterminal", "zeroOrMore", "oneOrMore", "terminal", "optional", "sequence", "special", "choice"}

var punctuation = [...][]string{
	Constructor: {"=", ";", "(", ",", ")"},
	EBNF:        {"::=", "=", ";", "|", ",", "(", ")", "[", "]", "{", "}", "?", "*", "+", "-"},
	ABNF:        {"=", ";", "/", "(", ")", "[", "]"},
	PEG:         {"<-", ";", "/", "(", ")", "&", "!", "?", "*", "+", "."},
}

type scanner struct {
	orig        string
	src         string
	removed     []source.Span
	n           Notation
	at          int
	tokens      []Token
	noYamlClose bool
}

func lex(text string, removed []source.Span, n Notation) []Token {
	s := &scanner{orig: text, src: blank(text, removed), removed: removed, n: n}
	s.run()
	return s.tokens
}

func blank(text string, removed []source.Span) string {
	b := []byte(text)
	for _, span := range removed {
		for i := max(span.Start, 0); i < min(span.End, len(b)); i++ {
			b[i] = ' '
		}
	}
	return string(b)
}

func (s *scanner) slice(start, end int) string {
	cuts := false
	for _, span := range s.removed {
		if span.Start < end && span.End > start {
			cuts = true
			break
		}
	}
	if !cuts {
		return s.orig[start:end]
	}
	var b strings.Builder
	for i := start; i < end; i++ {
		if !s.inRemoved(i) {
			b.WriteByte(s.orig[i])
		}
	}
	return b.String()
}

func (s *scanner) inRemoved(i int) bool {
	for _, span := range s.removed {
		if span.Start <= i && i < span.End {
			return true
		}
	}
	return false
}

func (s *scanner) emit(kind string, end int) {
	s.tokens = append(s.tokens, Token{Kind: kind, Text: s.slice(s.at, end), Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) terminate(opener string, from int) {
	s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: opener, Span: source.Span{Start: from, End: len(s.src)}})
	s.at = len(s.src)
}

func (s *scanner) run() {
	for s.at < len(s.src) {
		switch s.src[s.at] {
		case ' ', '\t', '\r', '\n':
			s.at++
			continue
		}
		if s.hidden() {
			continue
		}
		s.token()
	}
	end := len(s.src)
	s.tokens = append(s.tokens, Token{Kind: "EOF", Span: source.Span{Start: end, End: end}})
}

func (s *scanner) rest() string { return s.src[s.at:] }

func (s *scanner) lineEnd(from int) int {
	for i := from; i < len(s.src); i++ {
		if s.src[i] == '\n' || s.src[i] == '\r' {
			return i
		}
	}
	return len(s.src)
}

func (s *scanner) valueEnd(from int) int {
	end := s.lineEnd(from)
	for i := from; i+1 < end; i++ {
		if s.src[i] == '%' && s.src[i+1] == '%' {
			return i
		}
	}
	return end
}

func (s *scanner) hidden() bool {
	for _, rule := range [...]func() bool{s.percentComment, s.frontmatterBlock, s.blockComment, s.isoComment, s.abnfComment, s.pegComment} {
		if rule() {
			return true
		}
	}
	return false
}

func (s *scanner) percentComment() bool {
	if !strings.HasPrefix(s.rest(), "%%") {
		return false
	}
	s.at = s.lineEnd(s.at)
	return true
}

func (s *scanner) frontmatterBlock() bool {
	if !strings.HasPrefix(s.rest(), "---") {
		return false
	}
	end, ok := s.yaml()
	if ok {
		s.at = end
	}
	return ok
}

func (s *scanner) blockComment() bool {
	if !strings.HasPrefix(s.rest(), "/*") || (s.n != Constructor && s.n != EBNF) {
		return false
	}
	idx := strings.Index(s.src[s.at+2:], "*/")
	if idx < 0 {
		s.terminate("/*", s.at)
		return true
	}
	s.at += 2 + idx + 2
	return true
}

func (s *scanner) abnfComment() bool {
	if s.n != ABNF || s.src[s.at] != ';' {
		return false
	}
	if next := s.at + 1; next >= len(s.src) || s.src[next] == '\n' || s.src[next] == '\r' {
		return false
	}
	s.at = s.lineEnd(s.at)
	return true
}

func (s *scanner) pegComment() bool {
	if s.n != PEG || s.src[s.at] != '#' {
		return false
	}
	s.at = s.lineEnd(s.at)
	return true
}

func (s *scanner) isoComment() bool {
	if s.n != EBNF || !strings.HasPrefix(s.rest(), "(*") {
		return false
	}
	idx := strings.Index(s.src[s.at+2:], "*)")
	if idx < 0 {
		return false
	}
	s.at += 2 + idx + 2
	return true
}

func (s *scanner) yamlBodyStart() (int, bool) {
	i := s.horizontal(s.at + 3)
	if i < len(s.src) && s.src[i] == '\r' {
		i++
	}
	if i >= len(s.src) || s.src[i] != '\n' {
		return 0, false
	}
	return i + 1, true
}

func (s *scanner) yaml() (int, bool) {
	if s.noYamlClose {
		return 0, false
	}
	line, ok := s.yamlBodyStart()
	if !ok {
		return 0, false
	}
	for line >= 0 {
		if end, closed := s.yamlClosesAt(line); closed {
			return end, true
		}
		line = s.nextLine(line)
	}
	s.noYamlClose = true
	return 0, false
}

func (s *scanner) yamlClosesAt(line int) (int, bool) {
	if !strings.HasPrefix(s.src[line:], "---") {
		return 0, false
	}
	return s.yamlClose(line + 3)
}

func (s *scanner) nextLine(from int) int {
	next := strings.IndexByte(s.src[from:], '\n')
	if next < 0 {
		return -1
	}
	return from + next + 1
}

func (s *scanner) yamlClose(after int) (int, bool) {
	switch {
	case after < len(s.src) && s.src[after] == '\n':
		return after + 1, true
	case strings.HasPrefix(s.src[after:], "\r\n"):
		return after + 2, true
	case after >= len(s.src):
		return after, true
	}
	r, _ := utf8.DecodeRuneInString(s.src[after:])
	return after, jsSpace(r)
}

func (s *scanner) token() {
	for _, rule := range [...]func() bool{s.header, s.wordKeyword, s.special, s.punct, s.meta, s.identifier, s.quoted, s.numval, s.repeat} {
		if rule() {
			return
		}
	}
	_, size := utf8.DecodeRuneInString(s.rest())
	s.emit("INVALID", s.at+size)
}

func (s *scanner) meta() bool {
	switch rest := s.rest(); {
	case strings.HasPrefix(rest, "title"):
		s.emit("TITLE", s.titleEnd())
		return true
	case strings.HasPrefix(rest, "accTitle"):
		return s.accTitle()
	case strings.HasPrefix(rest, "accDescr"):
		return s.accDescr()
	}
	return false
}

func (s *scanner) identifier() bool {
	length := s.idLen()
	if length == 0 {
		return false
	}
	s.emit("ID", s.at+length)
	return true
}

func (s *scanner) quoted() bool {
	if c := s.src[s.at]; c == '"' || (c == '\'' && s.n != ABNF) {
		s.str()
		return true
	}
	return false
}

func (s *scanner) header() bool {
	keyword := headers[s.n]
	end := s.at + len(keyword)
	if end > len(s.src) || !equalFoldASCII(s.src[s.at:end], keyword) {
		return false
	}
	if end < len(s.src) && !strings.HasPrefix(s.src[end:], "%%") {
		if r, _ := utf8.DecodeRuneInString(s.src[end:]); !jsSpace(r) {
			return false
		}
	}
	s.emit("HEADER", end)
	return true
}

func equalFoldASCII(a, b string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range len(a) {
		x, y := a[i], b[i]
		if x >= 'A' && x <= 'Z' {
			x += 'a' - 'A'
		}
		if y >= 'A' && y <= 'Z' {
			y += 'a' - 'A'
		}
		if x != y {
			return false
		}
	}
	return true
}

func (s *scanner) wordKeyword() bool {
	if s.n != Constructor {
		return false
	}
	for _, keyword := range wordKeywords {
		if strings.HasPrefix(s.rest(), keyword) {
			if s.idLen() > len(keyword) {
				return false
			}
			s.emit(keyword, s.at+len(keyword))
			return true
		}
	}
	return false
}

func (s *scanner) special() bool {
	if s.n != EBNF || s.src[s.at] != '?' {
		return false
	}
	i := s.at + 1
	for i < len(s.src) && s.src[i] != '?' && s.src[i] != ';' {
		i++
	}
	if i >= len(s.src) || s.src[i] != '?' {
		return false
	}
	body := s.src[s.at+1 : i]
	if strings.TrimFunc(body, jsSpace) == "" {
		return false
	}
	s.emit("SPECIAL", i+1)
	return true
}

func (s *scanner) punct() bool {
	for _, p := range punctuation[s.n] {
		if strings.HasPrefix(s.rest(), p) {
			s.emit(p, s.at+len(p))
			return true
		}
	}
	return false
}

func (s *scanner) titleEnd() int {
	i := s.at + len("title")
	if i < len(s.src) && (s.src[i] == ' ' || s.src[i] == '\t') {
		return s.valueEnd(i + 1)
	}
	return i
}

func (s *scanner) horizontal(from int) int {
	for from < len(s.src) && (s.src[from] == ' ' || s.src[from] == '\t') {
		from++
	}
	return from
}

func (s *scanner) accTitle() bool {
	i := s.horizontal(s.at + len("accTitle"))
	if i >= len(s.src) || s.src[i] != ':' {
		return false
	}
	s.emit("ACC_TITLE", s.valueEnd(i+1))
	return true
}

func (s *scanner) accDescr() bool {
	after := s.at + len("accDescr")
	if i := s.horizontal(after); i < len(s.src) && s.src[i] == ':' {
		s.emit("ACC_DESCR", s.valueEnd(i+1))
		return true
	}
	i := after
	for i < len(s.src) {
		r, size := utf8.DecodeRuneInString(s.src[i:])
		if !jsSpace(r) {
			break
		}
		i += size
	}
	if i >= len(s.src) || s.src[i] != '{' {
		return false
	}
	idx := strings.IndexByte(s.src[i:], '}')
	if idx < 0 {
		s.terminate("{", i)
		return true
	}
	s.emit("ACC_DESCR", i+idx+1)
	return true
}

func asciiLetter(c byte) bool { return c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z' }

func (s *scanner) idStart(c byte) bool { return asciiLetter(c) || c == '_' && s.n != ABNF }

func (s *scanner) idPart(c byte) bool { return s.idStart(c) || c >= '0' && c <= '9' || c == '-' }

func (s *scanner) idLen() int {
	if !s.idStart(s.src[s.at]) {
		return 0
	}
	i := s.at + 1
	for i < len(s.src) && s.idPart(s.src[i]) {
		i++
	}
	return i - s.at
}

func (s *scanner) str() {
	quote := s.src[s.at]
	for i := s.at + 1; i < len(s.src); {
		switch c := s.src[i]; {
		case c == quote:
			s.emit("STRING", i+1)
			return
		case c == '\\' && s.n != ABNF:
			if i+1 >= len(s.src) {
				s.terminate(string(quote), s.at)
				return
			}
			r, size := utf8.DecodeRuneInString(s.src[i+1:])
			if lineTerminator(r) {
				s.emit("INVALID", s.at+1)
				return
			}
			i += 1 + size
		default:
			i++
		}
	}
	s.terminate(string(quote), s.at)
}

func hexDigit(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F'
}

func (s *scanner) hexRun(from int) int {
	for from < len(s.src) && hexDigit(s.src[from]) {
		from++
	}
	return from
}

func (s *scanner) numval() bool {
	i := s.at + 1
	if i >= len(s.src) || !strings.ContainsRune("xXdDbB", rune(s.src[i])) {
		return false
	}
	end := s.hexRun(i + 1)
	if end == i+1 {
		return false
	}
	for end < len(s.src) && (s.src[end] == '-' || s.src[end] == '.') {
		next := s.hexRun(end + 1)
		if next == end+1 {
			break
		}
		end = next
	}
	s.emit("NUMVAL", end)
	return true
}

func (s *scanner) repeat() bool {
	digits := s.at
	for digits < len(s.src) && s.src[digits] >= '0' && s.src[digits] <= '9' {
		digits++
	}
	if digits < len(s.src) && s.src[digits] == '*' {
		end := digits + 1
		for end < len(s.src) && s.src[end] >= '0' && s.src[end] <= '9' {
			end++
		}
		s.emit("REPEAT", end)
		return true
	}
	if digits > s.at {
		s.emit("EXACT_REPEAT", digits)
		return true
	}
	return false
}
