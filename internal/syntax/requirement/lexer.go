package requirement

import (
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var Modes = []string{"INITIAL", "string", "token", "unqString", "style", "acc_title", "acc_descr", "acc_descr_multiline"}

type Token struct {
	Kind string
	Text string
	Span source.Span
}

func Lex(src []byte, removed []source.Span) []Token {
	return lex(source.Clean(src, removed))
}

func lex(cleaned *source.Cleaned) []Token {
	l := lexer{src: string(cleaned.Text), cleaned: cleaned}
	return l.run()
}

type lexer struct {
	src        string
	cleaned    *source.Cleaned
	at         int
	mode       string
	headerSeen bool
	tokens     []Token
}

func (l *lexer) rest() string {
	if l.at >= len(l.src) {
		return ""
	}
	return l.src[l.at:]
}

func (l *lexer) emit(kind string, length int, text string) {
	l.emitSpan(kind, l.at, l.at+length, text)
}

func (l *lexer) emitSpan(kind string, start, end int, text string) {
	l.tokens = append(l.tokens, Token{Kind: kind, Text: text, Span: l.cleaned.Span(start, end)})
	l.at = end
}

func (l *lexer) raw(kind string, length int) {
	s := l.rest()
	if length > len(s) {
		length = len(s)
	}
	l.emit(kind, length, s[:length])
}

func (l *lexer) run() []Token {
	for l.at < len(l.src) {
		before := l.at
		l.next()
		if before == l.at {
			size := 1
			if _, s := utf8.DecodeRuneInString(l.rest()); s > 0 {
				size = s
			}
			l.raw("INVALID", size)
		}
	}
	l.raw("EOF", 0)
	return l.tokens
}

func (l *lexer) next() {
	if l.mode == "style" {
		l.styleMode()
		return
	}
	s := l.rest()
	if l.title(s) || l.accessibility(s) {
		return
	}
	line := lineLen(s)
	if kind := direction(s[:line]); kind != "" {
		l.raw(kind, line)
		return
	}
	if l.spaceOrComment(s) || l.header(s) || l.literal(s) {
		return
	}
	if strings.HasPrefix(s, "\"") {
		l.quoted()
		return
	}
	l.unquoted(s)
}

func (l *lexer) title(s string) bool {
	if !hasPrefixFold(s, "title") {
		return false
	}
	c, size := utf8.DecodeRuneInString(s[5:])
	if size == 0 || !unicode.IsSpace(c) {
		return false
	}
	value := s[5+size:]
	n := strings.IndexAny(value, "#\r\n;")
	if n < 0 {
		n = len(value)
	}
	if n == 0 {
		return false
	}
	l.raw("title", 5+size+n)
	return true
}

func (l *lexer) accessibility(s string) bool {
	for _, form := range [...][3]string{{"accTitle", "acc_title", "acc_title_value"}, {"accDescr", "acc_descr", "acc_descr_value"}} {
		if hasPrefixFold(s, form[0]) && l.accessibilityValue(s, form[0], form[1], form[2]) {
			return true
		}
	}
	return false
}

func (l *lexer) accessibilityValue(s, name, kind, valueKind string) bool {
	tail := strings.TrimLeftFunc(s[len(name):], unicode.IsSpace)
	if rest, ok := strings.CutPrefix(tail, ":"); ok {
		value := strings.TrimLeftFunc(rest, unicode.IsSpace)
		l.raw(kind, len(s)-len(value))
		l.raw(valueKind, lineLen(value))
		return true
	}
	if kind != "acc_descr" || !strings.HasPrefix(tail, "{") {
		return false
	}
	l.descriptionBlock(len(s) - len(tail))
	return true
}

func (l *lexer) descriptionBlock(brace int) {
	s := l.rest()
	content := strings.TrimLeftFunc(s[min(brace+1, len(s)):], unicode.IsSpace)
	n := strings.IndexByte(content, '}')
	if n < 0 {
		l.emitSpan("UNTERMINATED", l.at+brace, l.at+len(s), s[brace:])
		return
	}
	l.emit("acc_descr_multiline_value", len(s)-len(content)+n+1, content[:n])
}

func (l *lexer) spaceOrComment(s string) bool {
	if n := newlineRun(s); n > 0 {
		l.raw("NEWLINE", n)
		return true
	}
	n := 0
	for n < len(s) {
		r, size := utf8.DecodeRuneInString(s[n:])
		if !unicode.IsSpace(r) || r == '\r' || r == '\n' {
			break
		}
		n += size
	}
	if n > 0 {
		l.at += n
		return true
	}
	if strings.HasPrefix(s, "#") || strings.HasPrefix(s, "%%") {
		l.at += lineLen(s)
		return true
	}
	return false
}

func (l *lexer) header(s string) bool {
	if !l.headerSeen && strings.HasPrefix(s, "requirement") && isKeyword(s, "requirement") {
		l.headerSeen = true
		l.raw("RD", 11)
		return true
	}
	if strings.HasPrefix(s, "requirementDiagram") && isKeyword(s, "requirementDiagram") {
		l.headerSeen = true
		l.raw("RD", 18)
		return true
	}
	return false
}

func (l *lexer) literal(s string) bool {
	for _, form := range [...][2]string{
		{"{", "STRUCT_START"},
		{"}", "STRUCT_STOP"},
		{":::", "STYLE_SEPARATOR"},
		{":", "COLONSEP"},
		{"<-", "END_ARROW_L"},
		{"->", "END_ARROW_R"},
		{"-", "LINE"},
	} {
		if strings.HasPrefix(s, form[0]) {
			l.raw(form[1], len(form[0]))
			return true
		}
	}
	return l.bodyKeyword(s)
}

func (l *lexer) bodyKeyword(s string) bool {
	for _, form := range keywords {
		if !isKeyword(s, form[0]) {
			continue
		}
		switch form[1] {
		case "STYLE", "CLASSDEF", "CLASS":
			l.mode = "style"
		}
		l.raw(form[1], len(form[0]))
		return true
	}
	return false
}

func (l *lexer) quoted() {
	s := l.rest()
	content := s[1:]
	if n := strings.IndexByte(content, '"'); n >= 0 {
		l.emit("qString", n+2, content[:n])
		return
	}
	l.raw("UNTERMINATED", len(s))
}

func (l *lexer) unquoted(s string) {
	if !wordByte(s[0]) {
		l.universal(s)
		return
	}
	n := strings.IndexAny(s, ":,\r\n{<->=")
	if n < 0 {
		n = len(s)
	}
	l.emit("unqString", n, strings.TrimSpace(s[:n]))
}

func (l *lexer) styleMode() {
	s := l.rest()
	n := 0
	for n < len(s) && wordByte(s[n]) {
		n++
	}
	if n > 0 {
		l.raw("ALPHA", n)
		return
	}
	if strings.HasPrefix(s, "\"") {
		l.quoted()
		return
	}
	if e := endingLen(s); e > 0 {
		l.at += e
		l.mode = "INITIAL"
		return
	}
	if strings.HasPrefix(s, " ") {
		l.at++
		return
	}
	l.stylePunctuation(s)
}

func (l *lexer) stylePunctuation(s string) {
	for _, form := range [...][2]string{
		{":", "COLON"},
		{";", "SEMICOLON"},
		{"%", "PERCENT"},
		{"-", "MINUS"},
		{"#", "BRKT"},
	} {
		if strings.HasPrefix(s, form[0]) {
			l.raw(form[1], 1)
			return
		}
	}
	l.universal(s)
}

func (l *lexer) universal(s string) {
	n := 0
	for n < len(s) && wordByte(s[n]) {
		n++
	}
	if n > 0 {
		l.raw("ALPHA", n)
		return
	}
	if strings.HasPrefix(s, ",") {
		l.raw("COMMA", 1)
	}
}

var keywords = [...][2]string{
	{"id", "ID"},
	{"text", "TEXT"},
	{"risk", "RISK"},
	{"verifyMethod", "VERIFYMTHD"},
	{"requirement", "REQUIREMENT"},
	{"functionalRequirement", "FUNCTIONAL_REQUIREMENT"},
	{"interfaceRequirement", "INTERFACE_REQUIREMENT"},
	{"performanceRequirement", "PERFORMANCE_REQUIREMENT"},
	{"physicalRequirement", "PHYSICAL_REQUIREMENT"},
	{"designConstraint", "DESIGN_CONSTRAINT"},
	{"low", "LOW_RISK"},
	{"medium", "MED_RISK"},
	{"high", "HIGH_RISK"},
	{"analysis", "VERIFY_ANALYSIS"},
	{"demonstration", "VERIFY_DEMONSTRATION"},
	{"inspection", "VERIFY_INSPECTION"},
	{"test", "VERIFY_TEST"},
	{"element", "ELEMENT"},
	{"contains", "CONTAINS"},
	{"copies", "COPIES"},
	{"derives", "DERIVES"},
	{"satisfies", "SATISFIES"},
	{"verifies", "VERIFIES"},
	{"refines", "REFINES"},
	{"traces", "TRACES"},
	{"type", "TYPE"},
	{"docref", "DOCREF"},
	{"style", "STYLE"},
	{"classDef", "CLASSDEF"},
	{"class", "CLASS"},
}

func wordByte(b byte) bool {
	return b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' || b >= '0' && b <= '9' || b == '_'
}

func asciiLower(b byte) byte {
	if b >= 'A' && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

func hasPrefixFold(s, text string) bool {
	if len(s) < len(text) {
		return false
	}
	for i := range text {
		if asciiLower(s[i]) != asciiLower(text[i]) {
			return false
		}
	}
	return true
}

func isKeyword(s, text string) bool {
	return hasPrefixFold(s, text) && (len(s) == len(text) || !wordByte(s[len(text)]))
}

func lineLen(s string) int {
	if n := strings.IndexAny(s, "\r\n"); n >= 0 {
		return n
	}
	return len(s)
}

func endingLen(s string) int {
	switch {
	case strings.HasPrefix(s, "\r\n"):
		return 2
	case strings.HasPrefix(s, "\r"), strings.HasPrefix(s, "\n"):
		return 1
	}
	return 0
}

func direction(s string) string {
	for _, form := range [...][2]string{{"TB", "direction_tb"}, {"BT", "direction_bt"}, {"RL", "direction_rl"}, {"LR", "direction_lr"}} {
		if directionAxis(s, form[0]) {
			return form[1]
		}
	}
	return ""
}

func directionAxis(s, axis string) bool {
	for p := 0; p+9 <= len(s); p++ {
		if !hasPrefixFold(s[p:], "direction") {
			continue
		}
		tail := s[p+9:]
		value := strings.TrimLeftFunc(tail, unicode.IsSpace)
		if len(value) < len(tail) && hasPrefixFold(value, axis) {
			return true
		}
	}
	return false
}

func newlineRun(s string) int {
	length := 0
	for {
		n := endingLen(s[length:])
		if n == 0 {
			return length
		}
		length += n
	}
}
