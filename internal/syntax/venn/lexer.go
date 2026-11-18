package venn

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type lexMode uint8

const (
	modeInitial lexMode = iota
	modeBol
)

type fragment struct{ eff, orig int }

type lexer struct {
	src     string
	size    int
	frags   []fragment
	at      int
	mode    lexMode
	indent  bool
	consume bool
}

func newLexer(src string, removed []source.Span) *lexer {
	var kept strings.Builder
	var frags []fragment
	at := 0
	keep := func(to int) {
		if to > at {
			frags = append(frags, fragment{eff: kept.Len(), orig: at})
			kept.WriteString(src[at:to])
		}
	}
	for _, span := range removed {
		if span.Start < at || span.End > len(src) {
			continue
		}
		keep(span.Start)
		at = span.End
	}
	keep(len(src))
	return &lexer{src: kept.String(), size: len(src), frags: frags}
}

func (l *lexer) origin(at int) int {
	if at >= len(l.src) {
		return l.size
	}
	i := len(l.frags) - 1
	for i > 0 && l.frags[i].eff > at {
		i--
	}
	return l.frags[i].orig + at - l.frags[i].eff
}

func (l *lexer) span(start, end int) source.Span {
	if end <= start {
		at := l.origin(start)
		return source.Span{Start: at, End: at}
	}
	return source.Span{Start: l.origin(start), End: l.origin(end-1) + 1}
}

func sub(text string, from, to int) string {
	if from < 0 || to < from || to > len(text) {
		return ""
	}
	if from < len(text) && !utf8.RuneStart(text[from]) {
		return ""
	}
	if to < len(text) && !utf8.RuneStart(text[to]) {
		return ""
	}
	return text[from:to]
}

func isWordByte(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func isLetter(c byte) bool { return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' }

func isLineByte(c byte) bool { return c == '\n' || c == '\r' }

func isBlank(c byte) bool { return c == ' ' || c == '\t' }

func isHex(c byte) bool {
	return isDigit(c) || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F'
}

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func jsTrim(text string) string { return strings.TrimFunc(text, jsSpace) }

func foldByte(c byte) byte {
	if c >= 'A' && c <= 'Z' {
		return c + 'a' - 'A'
	}
	return c
}

func (l *lexer) matchFold(at int, word string) bool {
	if at+len(word) > len(l.src) {
		return false
	}
	for i := range len(word) {
		if foldByte(l.src[at+i]) != word[i] {
			return false
		}
	}
	return true
}

func (l *lexer) wordAt(at int, word string) bool {
	if !l.matchFold(at, word) {
		return false
	}
	end := at + len(word)
	return end >= len(l.src) || !isWordByte(l.src[end])
}

func (l *lexer) token(kind string, length int) Token {
	end := min(l.at+length, len(l.src))
	t := Token{Kind: kind, Text: sub(l.src, l.at, end), Span: l.span(l.at, end)}
	l.at = end
	return t
}

func (l *lexer) valued(kind, text string, length int) Token {
	end := min(l.at+length, len(l.src))
	t := Token{Kind: kind, Text: text, Span: l.span(l.at, end)}
	l.at = end
	return t
}

func (l *lexer) unterminated(opener string) Token {
	start := l.at
	l.at = len(l.src)
	return Token{Kind: "UNTERMINATED", Text: opener, Span: l.span(start, len(l.src))}
}

func (l *lexer) next() Token {
	for {
		if l.at >= len(l.src) {
			return Token{Kind: "EOF", Span: source.Span{Start: l.size, End: l.size}}
		}
		if t := l.step(); t.Kind != "" {
			return t
		}
	}
}

func (l *lexer) step() Token {
	if l.comment() {
		return Token{}
	}
	if l.mode == modeBol {
		if t, handled := l.lineStart(); handled {
			return t
		}
	}
	return l.body(l.src[l.at])
}

func (l *lexer) toLineEnd(from int) int {
	if i := strings.IndexAny(l.src[from:], "\r\n"); i >= 0 {
		return from + i
	}
	return len(l.src)
}

func (l *lexer) comment() bool {
	rest := l.src[l.at:]
	if strings.HasPrefix(rest, "%%") && !strings.HasPrefix(rest, "%%{") {
		l.at = l.toLineEnd(l.at)
		return true
	}
	r, size := utf8.DecodeRuneInString(rest)
	if r != '}' && size > 0 && strings.HasPrefix(rest[size:], "%%") {
		l.at = l.toLineEnd(l.at + size + 2)
		return true
	}
	return false
}

func (l *lexer) blanks(at int) int {
	n := 0
	for at+n < len(l.src) && isBlank(l.src[at+n]) {
		n++
	}
	return n
}

func (l *lexer) lineStart() (Token, bool) {
	if n := l.blanks(l.at); n > 0 {
		return l.indentedLine(n), true
	}
	if isLineByte(l.src[l.at]) {
		return Token{}, false
	}
	l.indent, l.mode = false, modeInitial
	return Token{}, true
}

func (l *lexer) indentedLine(n int) Token {
	if l.indent && l.wordAt(l.at+n, "text") {
		l.consume, l.mode = true, modeInitial
		return l.token("INDENT_TEXT", n)
	}
	l.at += n
	return Token{}
}

func (l *lexer) body(c byte) Token {
	switch {
	case isLineByte(c):
		return l.newline()
	case strings.HasPrefix(l.src[l.at:], "%%"):
		l.at = l.toLineEnd(l.at)
		return Token{}
	case isBlank(c):
		l.at += l.blanks(l.at)
		return Token{}
	}
	return l.word(c)
}

func (l *lexer) newline() Token {
	n := 1
	for l.at+n < len(l.src) && isLineByte(l.src[l.at+n]) {
		n++
	}
	l.mode = modeBol
	return l.token("NEWLINE", n)
}

var keywords = [...]struct{ text, kind string }{{"venn-beta", "VENN"}, {"set", "SET"}, {"union", "UNION"}, {"text", "TEXT"}, {"style", "STYLE"}}

func (l *lexer) word(c byte) Token {
	if t, ok := l.title(); ok {
		return t
	}
	for _, kw := range keywords {
		if !l.wordAt(l.at, kw.text) {
			continue
		}
		if kw.kind == "TEXT" && l.consume {
			l.consume = false
			l.at += len(kw.text)
			return Token{}
		}
		return l.token(kw.kind, len(kw.text))
	}
	return l.value(c)
}

func (l *lexer) title() (Token, bool) {
	if !l.matchFold(l.at, "title") {
		return Token{}, false
	}
	at := l.at + len("title")
	r, size := utf8.DecodeRuneInString(l.src[at:])
	if size == 0 || !jsSpace(r) {
		return Token{}, false
	}
	at += size
	n := 0
	for at+n < len(l.src) && l.src[at+n] != '#' && !isLineByte(l.src[at+n]) && l.src[at+n] != ';' {
		n++
	}
	if n == 0 {
		return Token{}, false
	}
	return l.token("TITLE", at+n-l.at), true
}

func (l *lexer) value(c byte) Token {
	switch c {
	case '[':
		return l.bracket()
	case '"':
		return l.quoted()
	case ',':
		return l.token("COMMA", 1)
	case ':':
		return l.token("COLON", 1)
	}
	return l.literal()
}

func (l *lexer) literal() Token {
	for _, rule := range [...]struct {
		kind  string
		match func() int
	}{
		{"NUMERIC", func() int { return l.number(l.at) }},
		{"HEXCOLOR", l.hexColour},
		{"RGBACOLOR", func() int { return l.colour("rgba", 4) }},
		{"RGBCOLOR", func() int { return l.colour("rgb", 3) }},
		{"IDENTIFIER", l.identifier},
	} {
		if n := rule.match(); n > 0 {
			return l.token(rule.kind, n)
		}
	}
	_, size := utf8.DecodeRuneInString(l.src[l.at:])
	return l.token("INVALID", max(size, 1))
}

func (l *lexer) hexColour() int {
	if l.src[l.at] != '#' {
		return 0
	}
	n := 0
	for n < 8 && l.at+1+n < len(l.src) && isHex(l.src[l.at+1+n]) {
		n++
	}
	if n < 3 {
		return 0
	}
	return 1 + n
}

func (l *lexer) identifier() int {
	c := l.src[l.at]
	if c != '_' && !isLetter(c) {
		return 0
	}
	n := 1
	for l.at+n < len(l.src) && (isWordByte(l.src[l.at+n]) || l.src[l.at+n] == '-') {
		n++
	}
	return n
}

func (l *lexer) quoted() Token {
	i := strings.IndexByte(l.src[l.at+1:], '"')
	if i < 0 {
		return l.unterminated("\"")
	}
	return l.token("STRING", i+2)
}

func (l *lexer) bracket() Token {
	rest := l.src[l.at+1:]
	if strings.HasPrefix(rest, "\"") {
		return l.quotedBracket(rest[1:])
	}
	i := strings.IndexAny(rest, "]\"")
	switch {
	case i < 0:
		return l.unterminated("[")
	case i == 0 || rest[i] == '"':
		return l.token("INVALID", 1)
	}
	return l.valued("BRACKET_LABEL", jsTrim(rest[:i]), i+2)
}

func (l *lexer) quotedBracket(afterQuote string) Token {
	i := strings.IndexByte(afterQuote, '"')
	switch {
	case i < 0 || i+1 >= len(afterQuote):
		return l.unterminated("[")
	case afterQuote[i+1] != ']':
		return l.token("INVALID", 1)
	}
	return l.valued("BRACKET_LABEL", afterQuote[:i], i+4)
}

func (l *lexer) digits(at int) int {
	n := 0
	for at+n < len(l.src) && isDigit(l.src[at+n]) {
		n++
	}
	return n
}

func (l *lexer) fraction(at int) int {
	if at+1 < len(l.src) && l.src[at] == '.' && isDigit(l.src[at+1]) {
		return 1 + l.digits(at+1)
	}
	return 0
}

func (l *lexer) number(at int) int {
	start := at
	if at < len(l.src) && (l.src[at] == '+' || l.src[at] == '-') {
		at++
	}
	whole := l.digits(at)
	at += whole
	frac := l.fraction(at)
	if whole == 0 && frac == 0 {
		return 0
	}
	return at + frac - start
}

func (l *lexer) spaces(at int) int {
	n := 0
	for at+n < len(l.src) {
		r, size := utf8.DecodeRuneInString(l.src[at+n:])
		if size == 0 || !jsSpace(r) {
			break
		}
		n += size
	}
	return n
}

func (l *lexer) colourPart(at int, want byte) int {
	at += l.spaces(at)
	digits := 0
	for at+digits < len(l.src) && (isDigit(l.src[at+digits]) || l.src[at+digits] == '.') {
		digits++
	}
	if digits == 0 {
		return -1
	}
	at += digits
	at += l.spaces(at)
	if at >= len(l.src) || l.src[at] != want {
		return -1
	}
	return at + 1
}

func (l *lexer) colour(name string, parts int) int {
	if !l.matchFold(l.at, name) || l.at+len(name) >= len(l.src) || l.src[l.at+len(name)] != '(' {
		return 0
	}
	at := l.at + len(name) + 1
	for i := range parts {
		want := byte(',')
		if i == parts-1 {
			want = ')'
		}
		if at = l.colourPart(at, want); at < 0 {
			return 0
		}
	}
	return at - l.at
}
