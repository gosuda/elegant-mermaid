package er

import (
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type lexer struct {
	src     []byte
	cleaned *source.Cleaned
	at      int
	mode    string
	tokens  []Token
}

func Lex(src []byte, removed []source.Span) []Token {
	return lex(source.Clean(src, removed))
}

func lex(cleaned *source.Cleaned) []Token {
	l := &lexer{src: cleaned.Text, cleaned: cleaned, mode: "INITIAL"}
	for l.at < len(l.src) {
		l.next()
	}
	if l.mode == "acc_title" || l.mode == "acc_descr" {
		l.accessibilityValue()
	}
	l.emit("EOF", 0)
	return l.tokens
}

func (l *lexer) rest() string {
	return string(l.src[min(l.at, len(l.src)):])
}

func (l *lexer) emit(kind string, length int) {
	end := l.at + length
	l.tokens = append(l.tokens, Token{Kind: kind, Text: string(l.src[l.at:end]), Span: l.cleaned.Span(l.at, end)})
	l.at = end
}

func (l *lexer) value(kind string, span source.Span, text string) {
	l.tokens = append(l.tokens, Token{Kind: kind, Text: text, Span: l.cleaned.Span(span.Start, span.End)})
	l.at = span.End
}

func (l *lexer) next() {
	switch l.mode {
	case "acc_title", "acc_descr":
		l.accessibilityValue()
	case "style":
		l.styleMode()
	case "block":
		l.blockMode()
	default:
		l.initialMode()
	}
}

func (l *lexer) initialMode() {
	s := l.rest()
	if l.accessibility() {
		return
	}
	line := lineLen(s)
	if kind, ok := directionToken(s[:line]); ok {
		l.emit(kind, line)
		return
	}
	if l.spaceOrNewline() || l.quoted() || l.initialSymbol() {
		return
	}
	if l.keyword() || l.relationship() || l.number() {
		return
	}
	if n := charRun(s, textChar); n > 0 {
		l.emit("UNICODE_TEXT", n)
		return
	}
	l.literal()
}

func (l *lexer) initialSymbol() bool {
	for _, pair := range [][2]string{
		{"{", "BLOCK_START"},
		{"#", "BRKT"},
		{",", "COMMA"},
		{":::", "STYLE_SEPARATOR"},
		{":", "COLON"},
		{"[", "SQS"},
		{"]", "SQE"},
	} {
		if strings.HasPrefix(l.rest(), pair[0]) {
			l.emit(pair[1], len(pair[0]))
			if pair[1] == "BLOCK_START" {
				l.mode = "block"
			}
			return true
		}
	}
	return false
}

func (l *lexer) keyword() bool {
	for _, pair := range [][2]string{
		{"erDiagram", "ER_DIAGRAM"},
		{"style", "STYLE"},
		{"classDef", "CLASSDEF"},
		{"class", "CLASS"},
		{"subgraph", "SUBGRAPH"},
		{"end", "END"},
	} {
		text, kind := pair[0], pair[1]
		if !asciiPrefix(l.rest(), text) || !l.keywordBoundary(text, kind) {
			continue
		}
		n := len(text)
		if kind == "END" {
			n += charRun(l.rest()[n:], unicode.IsSpace)
		}
		l.emit(kind, n)
		if kind == "STYLE" || kind == "CLASSDEF" {
			l.mode = "style"
		}
		return true
	}
	return false
}

func (l *lexer) keywordBoundary(text, kind string) bool {
	tail := ""
	if l.at+len(text) <= len(l.src) {
		tail = string(l.src[l.at+len(text):])
	}
	next, _ := utf8.DecodeRuneInString(tail)
	switch kind {
	case "ER_DIAGRAM":
		return strings.HasPrefix(l.rest(), text) && !isAlnumASCII(next) && next != '-' && next != '_'
	case "END":
		return !asciiWord(next)
	}
	return true
}

func (l *lexer) relationship() bool {
	if l.cardinalityWord() {
		return true
	}
	if strings.HasPrefix(l.rest(), "1") && contextualOne(l.rest()) {
		l.emit("ONLY_ONE", 1)
		return true
	}
	rest := l.rest()
	if asciiPrefix(rest, "u") && len(rest) > 1 && mdParentNext(rest[1]) {
		l.emit("MD_PARENT", 1)
		return true
	}
	for _, pair := range [][2]string{
		{"..", "NON_IDENTIFYING"},
		{"--", "IDENTIFYING"},
		{"to", "IDENTIFYING"},
		{"optionally to", "NON_IDENTIFYING"},
		{".-", "NON_IDENTIFYING"},
		{"-.", "NON_IDENTIFYING"},
	} {
		if relationshipPrefix(l.rest(), pair[0]) {
			l.emit(pair[1], len(pair[0]))
			return true
		}
	}
	return false
}

func (l *lexer) cardinalityWord() bool {
	for _, pair := range [][2]string{
		{"one or zero", "ZERO_OR_ONE"},
		{"one or more", "ONE_OR_MORE"},
		{"one or many", "ONE_OR_MORE"},
		{"1+", "ONE_OR_MORE"},
		{"|o", "ZERO_OR_ONE"},
		{"zero or one", "ZERO_OR_ONE"},
		{"zero or more", "ZERO_OR_MORE"},
		{"zero or many", "ZERO_OR_MORE"},
		{"0+", "ZERO_OR_MORE"},
		{"}o", "ZERO_OR_MORE"},
		{"many(0)", "ZERO_OR_MORE"},
		{"many(1)", "ONE_OR_MORE"},
		{"many", "ZERO_OR_MORE"},
		{"}|", "ONE_OR_MORE"},
		{"one", "ONLY_ONE"},
		{"only one", "ONLY_ONE"},
		{"||", "ONLY_ONE"},
		{"o|", "ZERO_OR_ONE"},
		{"o{", "ZERO_OR_MORE"},
		{"|{", "ONE_OR_MORE"},
	} {
		if asciiPrefix(l.rest(), pair[0]) {
			l.emit(pair[1], len(pair[0]))
			return true
		}
	}
	return false
}

func digitRun(s string) int {
	n := 0
	for n < len(s) && s[n] >= '0' && s[n] <= '9' {
		n++
	}
	return n
}

func decimalEnd(s string, integers int) (int, bool) {
	if integers >= len(s) || s[integers] != '.' {
		return 0, false
	}
	fraction := digitRun(s[integers+1:])
	return integers + 1 + fraction, fraction > 0
}

func (l *lexer) number() bool {
	integers := digitRun(l.rest())
	if integers == 0 {
		return false
	}
	if end, ok := decimalEnd(l.rest(), integers); ok {
		l.emit("DECIMAL_NUM", end)
		return true
	}
	if l.rest()[0] == '1' {
		l.emit("ENTITY_ONE", 1)
		return true
	}
	l.emit("NUM", integers)
	return true
}

func (l *lexer) spaceOrNewline() bool {
	s := l.rest()
	if n := charRun(s, func(c rune) bool { return c == ' ' || c == '\t' }); n > 0 {
		l.at += n
		return true
	}
	n := newlineRun(s)
	if n == 0 {
		return false
	}
	l.emit("NEWLINE", n)
	return true
}

func (l *lexer) quoted() bool {
	s := l.rest()
	if !strings.HasPrefix(s, "\"") {
		return false
	}
	tail := s[1:]
	n := strings.IndexByte(tail, '"')
	if n < 0 {
		l.value("UNTERMINATED", source.Span{Start: l.at, End: len(l.src)}, "\"")
		return true
	}
	value := tail[:n]
	kind := "WORD"
	if l.mode == "block" {
		kind = "COMMENT"
	} else if value != "" && !strings.ContainsAny(value, "%\r\n\v\b\\") {
		kind = "ENTITY_NAME"
	}
	l.value(kind, source.Span{Start: l.at, End: l.at + n + 2}, value)
	return true
}

func (l *lexer) accessibility() bool {
	for _, pair := range [][2]string{{"accTitle", "acc_title"}, {"accDescr", "acc_descr"}} {
		name, kind := pair[0], pair[1]
		s := l.rest()
		if !asciiPrefix(s, name) {
			continue
		}
		tail := s[len(name):]
		ws := charRun(tail, unicode.IsSpace)
		tail = tail[ws:]
		if strings.HasPrefix(tail, ":") {
			after := tail[1:]
			l.emit(kind, len(name)+ws+1+charRun(after, unicode.IsSpace))
			l.mode = kind
			return true
		}
		if kind == "acc_descr" && strings.HasPrefix(tail, "{") {
			l.accessibilityBlock(len(name) + ws)
			return true
		}
	}
	return false
}

func (l *lexer) accessibilityValue() {
	kind := "acc_descr_value"
	if l.mode == "acc_title" {
		kind = "acc_title_value"
	}
	l.mode = "INITIAL"
	l.emit(kind, lineLen(l.rest()))
}

func (l *lexer) accessibilityBlock(brace int) {
	l.mode = "acc_descr_multiline"
	start := l.at
	body := string(l.src[l.at+brace+1:])
	if n := strings.IndexByte(body, '}'); n >= 0 {
		l.value("acc_descr_multiline_value", source.Span{Start: start, End: start + brace + n + 2}, strings.TrimLeftFunc(body[:n], unicode.IsSpace))
	} else {
		l.value("UNTERMINATED", source.Span{Start: start + brace, End: len(l.src)}, "{")
	}
	l.mode = "INITIAL"
}

func (l *lexer) blockMode() {
	s := l.rest()
	if ws := charRun(s, unicode.IsSpace); ws > 0 {
		l.at += ws
		return
	}
	if l.attributeKey() || l.genericWord() {
		return
	}
	if first, _ := utf8.DecodeRuneInString(s); attributeStart(first) {
		l.emit("ATTRIBUTE_WORD", charRun(s, attributeChar))
		return
	}
	if strings.HasPrefix(s, "`") {
		l.backtick()
		return
	}
	if l.quoted() {
		return
	}
	if strings.HasPrefix(s, "}") {
		l.emit("BLOCK_STOP", 1)
		l.mode = "INITIAL"
		return
	}
	l.literal()
}

func (l *lexer) attributeKey() bool {
	before, size := utf8.DecodeLastRune(l.src[:l.at])
	if l.at > 0 && size > 0 && asciiWord(before) {
		return false
	}
	for _, key := range []string{"PK", "FK", "UK"} {
		s := l.rest()
		if !asciiPrefix(s, key) {
			continue
		}
		next, size := utf8.DecodeRuneInString(s[2:])
		if size == 0 || !asciiWord(next) {
			l.emit("ATTRIBUTE_KEY", 2)
			return true
		}
	}
	return false
}

func (l *lexer) genericWord() bool {
	s := l.rest()
	line := s[:lineLen(s)]
	first := strings.IndexByte(line, '~')
	if first < 0 {
		return false
	}
	if strings.IndexFunc(line[:first], unicode.IsSpace) >= 0 {
		return false
	}
	last := strings.LastIndexByte(line, '~')
	if last <= first {
		return false
	}
	suffix := charRun(line[last+1:], func(c rune) bool { return !unicode.IsSpace(c) })
	l.emit("ATTRIBUTE_WORD", last+1+suffix)
	return true
}

func (l *lexer) backtick() {
	l.mode = "block_bq"
	start := l.at
	body := string(l.src[l.at+1:])
	n := strings.IndexByte(body, '`')
	switch {
	case n < 0:
		l.value("UNTERMINATED", source.Span{Start: start, End: len(l.src)}, "`")
	case n == 0:
		l.at += 2
	default:
		l.value("ATTRIBUTE_WORD", source.Span{Start: start, End: start + n + 2}, body[:n])
	}
	l.mode = "block"
}

func (l *lexer) styleMode() {
	s := l.rest()
	if n := newlineRun(s); n > 0 {
		l.emit("NEWLINE", n)
		l.mode = "INITIAL"
		return
	}
	if ws := charRun(s, unicode.IsSpace); ws > 0 {
		l.at += ws
		return
	}
	for _, pair := range [][2]string{{":", "COLON"}, {",", "COMMA"}, {"#", "BRKT"}, {";", "SEMI"}} {
		if strings.HasPrefix(s, pair[0]) {
			l.emit(pair[1], 1)
			return
		}
	}
	if n := charRun(s, styleChar); n > 0 {
		l.emit("STYLE_TEXT", n)
		return
	}
	l.literal()
}

func (l *lexer) literal() {
	_, size := utf8.DecodeRune(l.src[l.at:])
	kind := "INVALID"
	for _, text := range []string{
		"?", ",", ";", "{", "}", "(", ")", "[", "]", "%", ":", "#", "|", "+", "=", "/", "\\", "\"", "'", "`", "!", "@", "$", "&", "^", "~", "<", ">", ".", "-",
	} {
		if strings.HasPrefix(l.rest(), text) {
			kind = text
			break
		}
	}
	if size == 0 {
		size = 1
	}
	l.emit(kind, size)
}

func asciiPrefix(s, text string) bool {
	if len(s) < len(text) {
		return false
	}
	for i := range len(text) {
		if foldASCII(s[i]) != foldASCII(text[i]) {
			return false
		}
	}
	return true
}

func mdParentNext(b byte) bool {
	return b == '.' || b == '-' || b == '|'
}

func foldASCII(b byte) byte {
	if 'A' <= b && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

func charRun(s string, predicate func(rune) bool) int {
	n := 0
	for n < len(s) {
		c, size := utf8.DecodeRuneInString(s[n:])
		if size == 0 || !predicate(c) {
			break
		}
		n += size
	}
	return n
}

func asciiWord(c rune) bool {
	return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9' || c == '_'
}

func isAlnumASCII(c rune) bool {
	return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c >= '0' && c <= '9'
}

func styleChar(c rune) bool {
	return c > 127 || asciiWord(c) || c == '-' || c == '*'
}

func textChar(c rune) bool {
	return styleChar(c) || c == '.'
}

func attributeStart(c rune) bool {
	return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '*' || c == '_' || c >= 0xC0 && c <= 0xFFFF
}

func attributeChar(c rune) bool {
	return attributeStart(c) || c >= '0' && c <= '9' || c == '-' || c == '[' || c == ']' || c == '(' || c == ')' || c == '.' || c == ','
}

func lineLen(s string) int {
	if n := strings.IndexAny(s, "\r\n"); n >= 0 {
		return n
	}
	return len(s)
}

func newlineRun(s string) int {
	n := 0
	for n < len(s) && (s[n] == '\r' || s[n] == '\n') {
		n++
	}
	return n
}

func contextualOne(s string) bool {
	tail := s[1:]
	for _, line := range []string{"--", "..", ".-", "-."} {
		if strings.HasPrefix(tail, line) {
			return true
		}
	}
	n := charRun(tail, unicode.IsSpace)
	if n == 0 {
		return false
	}
	next, _ := utf8.DecodeRuneInString(tail[n:])
	return isAlnumASCII(next) || next == '_' || next == '"' || next == '\''
}

func directionToken(line string) (string, bool) {
	for _, pair := range [][2]string{
		{"TB", "direction_tb"},
		{"BT", "direction_bt"},
		{"RL", "direction_rl"},
		{"LR", "direction_lr"},
	} {
		if directionAxis(line, pair[0]) {
			return pair[1], true
		}
	}
	return "", false
}

func directionAxis(line, axis string) bool {
	for i := range line {
		tail := line[i:]
		if !asciiPrefix(tail, "direction") {
			continue
		}
		tail = tail[len("direction"):]
		ws := charRun(tail, unicode.IsSpace)
		if ws > 0 && asciiPrefix(tail[ws:], axis) {
			return true
		}
	}
	return false
}

func relationshipPrefix(source, text string) bool {
	if !asciiPrefix(source, text) {
		return false
	}
	if !strings.HasSuffix(text, "to") {
		return true
	}
	if len(source) == len(text) {
		return true
	}
	next, _ := utf8.DecodeRuneInString(source[len(text):])
	return !asciiWord(next)
}
