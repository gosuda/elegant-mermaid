package class

import (
	"bytes"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Token struct {
	Kind string
	Text string
	Span source.Span
	Raw  []byte
}

type lexer struct {
	src          []byte
	at           int
	removed      []source.Span
	tokens       []Token
	classPending bool
	bodyDepth    int
}

func Lex(src []byte, removed []source.Span) []Token {
	l := lexer{src: src, removed: removed}
	for l.at < len(src) {
		l.next()
	}
	return l.tokens
}

func (l *lexer) emit(kind string, start, end int) {
	raw := l.src[start:end]
	l.tokens = append(l.tokens, Token{Kind: kind, Text: string(raw), Span: source.Span{Start: start, End: end}, Raw: raw})
}

func (l *lexer) skipRemoved() bool {
	for _, span := range l.removed {
		if l.at >= span.Start && l.at < span.End {
			l.at = span.End
			return true
		}
	}
	return false
}

func (l *lexer) next() {
	if l.skipRemoved() {
		return
	}
	if l.bodyDepth > 0 {
		l.memberToken()
		return
	}
	if l.directionLine() {
		return
	}
	start := l.at
	b := l.src[l.at]
	l.at++
	if b == ' ' || b == '\t' {
		return
	}
	if b == '\r' || b == '\n' {
		l.classPending = false
		l.newline(start, b)
		return
	}
	l.symbol(start, b)
}

func (l *lexer) newline(start int, b byte) {
	if b == '\r' && l.at < len(l.src) && l.src[l.at] == '\n' {
		l.at++
	}
	l.emit("NEWLINE", start, l.at)
}

func (l *lexer) symbol(start int, b byte) {
	if b == '"' || b == '`' || b == '~' {
		l.quoted(start, b)
		return
	}
	if bytes.HasPrefix(l.src[start:], []byte("%%")) {
		l.skipComment()
		return
	}
	if l.operator(start) {
		return
	}
	l.single(start, b)
}

func (l *lexer) skipComment() {
	for l.at < len(l.src) && l.src[l.at] != '\n' && l.src[l.at] != '\r' {
		l.at++
	}
}

func (l *lexer) operator(start int) bool {
	for _, op := range []string{"<|", "|>", "<<", ">>", "--", "..", "()", ":::"} {
		if bytes.HasPrefix(l.src[start:], []byte(op)) {
			l.at = start + len(op)
			l.emit(op, start, l.at)
			return true
		}
	}
	return false
}

func (l *lexer) single(start int, b byte) {
	if b == '{' && l.classPending {
		l.bodyDepth = 1
		l.classPending = false
	}
	if strings.ContainsRune("{}[]:;,*<>+-#%=()./!$&", rune(b)) {
		l.emit(string(b), start, l.at)
		return
	}
	if b >= 128 {
		l.unicodeToken(start)
		return
	}
	if wordByte(b) {
		l.word(start)
		return
	}
	l.emit("INVALID", start, l.at)
}

func (l *lexer) quoted(start int, quote byte) {
	for l.at < len(l.src) && l.src[l.at] != quote {
		l.at++
	}
	if l.at == len(l.src) {
		l.emit("UNTERMINATED", start, l.at)
		return
	}
	l.at++
	kind := map[byte]string{'"': "STR", '`': "BQUOTE_STR", '~': "GENERICTYPE"}[quote]
	l.emit(kind, start, l.at)
	l.tokens[len(l.tokens)-1].Text = string(l.src[start+1 : l.at-1])
}

func wordByte(b byte) bool {
	return b >= 'a' && b <= 'z' || b >= 'A' && b <= 'Z' || b >= '0' && b <= '9' || b == '_'
}

func (l *lexer) word(start int) {
	for l.at < len(l.src) && wordByte(l.src[l.at]) {
		l.at++
	}
	if string(l.src[start:l.at]) == "classDiagram" && bytes.HasPrefix(l.src[l.at:], []byte("-v2")) {
		l.at += 3
	}
	text := string(l.src[start:l.at])
	kind := keyword(text)
	if kind == "class" {
		l.classPending = true
	}
	l.emit(kind, start, l.at)
}

func (l *lexer) unicodeToken(start int) {
	cp, size := utf8.DecodeRune(l.src[start:])
	l.at = start + size
	kind := "INVALID"
	if classLetter(cp) {
		kind = "UNICODE_TEXT"
	}
	l.emit(kind, start, l.at)
}

func keyword(text string) string {
	for _, key := range []string{"class", "namespace", "style", "classDef", "cssClass", "callback", "link", "click", "call", "note", "for", "href", "direction", "accTitle", "accDescr", "classDiagram", "classDiagram-v2", "o"} {
		if text == key {
			return key
		}
	}
	return "ALPHA"
}

func (l *lexer) memberToken() {
	start := l.at
	b := l.src[l.at]
	switch b {
	case '}':
		l.bodyDepth--
		l.at++
		l.emit("}", start, l.at)
	case '{':
		l.bodyDepth++
		l.at++
		l.emit("{", start, l.at)
	case '\n', '\r':
		l.at++
		l.newline(start, b)
	default:
		for l.at < len(l.src) && !strings.ContainsRune("{}\r\n", rune(l.src[l.at])) {
			l.at++
		}
		l.emit("MEMBER", start, l.at)
	}
}
