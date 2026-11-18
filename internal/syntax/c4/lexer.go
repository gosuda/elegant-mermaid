package c4

import (
	"bytes"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type scanner struct {
	src      []byte
	cleaned  *source.Cleaned
	at       int
	mode     string
	opening  int
	argument int
	tokens   []Token
}

func Lex(src []byte, removed []source.Span) []Token {
	return lex(source.Clean(src, removed))
}

func lex(cleaned *source.Cleaned) []Token {
	s := scanner{src: cleaned.Text, cleaned: cleaned, mode: "INITIAL", opening: -1, argument: -1}
	s.run()
	return s.tokens
}

func (s *scanner) run() {
	for s.at < len(s.src) {
		beforeAt, beforeMode := s.at, s.mode
		s.next()
		if s.at == beforeAt && s.mode == beforeMode {
			size := runeLen(s.src[s.at:])
			s.raw("INVALID", s.at, s.at+size)
		}
	}
	s.finish()
}

func (s *scanner) raw(kind string, start, end int) {
	s.emit(kind, start, end, start, end)
}

func (s *scanner) emit(kind string, start, end, valueStart, valueEnd int) {
	raw := s.src[valueStart:valueEnd]
	s.tokens = append(s.tokens, Token{Kind: kind, Span: s.cleaned.Span(start, end), Raw: raw})
	s.at = end
}

func (s *scanner) finish() {
	if s.mode == "acc_title" || s.mode == "acc_descr" {
		s.lineValue()
	}
	if s.mode != "INITIAL" {
		start := s.unclosedStart()
		s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Span: s.cleaned.Span(start, len(s.src)), Raw: s.src[start:]})
	}
	s.tokens = append(s.tokens, Token{Kind: "EOF", Span: s.cleaned.Span(s.at, s.at)})
}

func (s *scanner) unclosedStart() int {
	if s.mode == "acc_descr_multiline" {
		return firstSet(s.opening, s.argument, s.at)
	}
	return firstSet(s.argument, s.opening, s.at)
}

func firstSet(values ...int) int {
	for _, value := range values {
		if value >= 0 {
			return value
		}
	}
	return -1
}

func (s *scanner) next() {
	switch s.mode {
	case "INITIAL":
		s.initial()
	case "attribute":
		s.attribute()
	case "string":
		s.quoted()
	case "string_kv":
		s.namedKey()
	case "string_kv_key":
		s.namedEquals()
	case "string_kv_value":
		s.namedValue()
	case "acc_title", "acc_descr":
		s.lineValue()
	case "acc_descr_multiline":
		s.descriptionBlock()
	default:
		s.callOpen()
	}
}

func (s *scanner) initial() {
	end := len(s.src)
	line := lineLen(s.src[s.at:end])
	if kind, ok := directionKind(s.src[s.at : s.at+line]); ok {
		s.raw(kind, s.at, s.at+line)
		return
	}
	switch {
	case s.metadata(end), s.whitespace(end), s.header(end), s.macroName(end):
		return
	}
	b := s.src[s.at:end]
	if len(b) > 0 && b[0] == '{' {
		s.raw("LBRACE", s.at, s.at+1)
		return
	}
	if len(b) > 0 && b[0] == '}' {
		s.raw("RBRACE", s.at, s.at+1)
		return
	}
	s.unknown(end)
}

func (s *scanner) metadata(end int) bool {
	for _, m := range [...]struct{ name, kind string }{{"title", "title"}, {"accDescription", "accDescription"}} {
		rest, ok := s.prefix(m.name, end)
		if !ok || !startsWithSpace(rest) {
			continue
		}
		length := indexAny(rest, "#\r\n;")
		if length <= 1 {
			continue
		}
		s.raw(m.kind, s.at, s.at+len(m.name)+length)
		return true
	}
	return s.accessibility(end)
}

func (s *scanner) accessibility(end int) bool {
	for _, a := range [...]struct{ name, mode string }{{"accTitle", "acc_title"}, {"accDescr", "acc_descr"}} {
		rest, ok := s.prefix(a.name, end)
		if !ok {
			continue
		}
		tail := trimLeftSpace(rest)
		prefix := end - s.at - len(tail)
		if len(tail) > 0 && tail[0] == ':' {
			ws := len(tail[1:]) - len(trimLeftSpace(tail[1:]))
			s.mode = a.mode
			s.raw(a.mode, s.at, s.at+prefix+1+ws)
			return true
		}
		if a.mode == "acc_descr" && len(tail) > 0 && tail[0] == '{' {
			s.opening = s.at + prefix
			s.argument = s.at
			s.mode = "acc_descr_multiline"
			s.at += prefix + 1
			return true
		}
	}
	return false
}

func (s *scanner) whitespace(end int) bool {
	b := s.src[s.at:end]
	if bytes.HasPrefix(b, []byte("%%")) {
		s.at += lineLen(b)
		return true
	}
	length := len(b) - len(trimLeftSpace(b))
	if length == 0 {
		return false
	}
	if bytes.ContainsAny(b[:length], "\r\n") {
		s.raw("NEWLINE", s.at, s.at+length)
	} else {
		s.at += length
	}
	return true
}

func (s *scanner) header(end int) bool {
	b := s.src[s.at:end]
	kind, size := headerKind(b)
	if size == 0 || headerBoundary(b[size:]) {
		return false
	}
	s.raw(kind, s.at, s.at+size)
	return true
}

func (s *scanner) macroName(end int) bool {
	b := s.src[s.at:end]
	name := macroNameCandidate(b)
	if !macroArguments(b[len(name):]) {
		return false
	}
	kind, ok := macroKind(name)
	if !ok {
		return false
	}
	s.mode = macroMode
	s.raw(kind, s.at, s.at+len(name))
	return true
}

func macroNameCandidate(b []byte) []byte {
	i := 0
	for i < len(b) && (b[i] == '_' || b[i] >= 'a' && b[i] <= 'z' || b[i] >= 'A' && b[i] <= 'Z') {
		i++
	}
	return b[:i]
}

func macroArguments(rest []byte) bool {
	trimmed := trimLeftSpace(rest)
	return len(trimmed) > 0 && trimmed[0] == '('
}

func (s *scanner) unknown(end int) {
	b := s.src[s.at:end]
	length := indexWhitespaceOrBrace(b)
	if size := runeLen(b); length < size {
		length = size
	}
	s.raw("INVALID", s.at, s.at+length)
}

func (s *scanner) callOpen() {
	end := len(s.src)
	b := s.src[s.at:end]
	trimmed := trimLeftSpace(b)
	if ws := len(b) - len(trimmed); ws > 0 {
		s.at += ws
		return
	}
	if len(b) == 0 || b[0] != '(' {
		return
	}
	s.opening = s.at
	s.raw("LPAREN", s.at, s.at+1)
	s.mode = "attribute"
	rest := s.src[s.at:]
	spaces := 0
	for spaces < len(rest) && rest[spaces] == ' ' {
		spaces++
	}
	if spaces < len(rest) && rest[spaces] == ',' {
		s.raw("ATTRIBUTE_EMPTY", s.at, s.at+spaces+1)
	}
}

func (s *scanner) attribute() {
	end := len(s.src)
	b := s.src[s.at:end]
	if len(b) > 0 && b[0] == ')' {
		s.raw("RPAREN", s.at, s.at+1)
		s.mode = "INITIAL"
		s.opening = -1
		return
	}
	if bytes.HasPrefix(b, []byte(",,")) {
		s.raw("ATTRIBUTE_EMPTY", s.at, s.at+2)
		return
	}
	if len(b) > 0 && b[0] == ',' {
		s.at++
		return
	}
	spaces := 0
	for spaces < len(b) && b[spaces] == ' ' {
		spaces++
	}
	rest := b[spaces:]
	if bytes.HasPrefix(rest, []byte(`""`)) {
		s.raw("ATTRIBUTE_EMPTY", s.at, s.at+spaces+2)
		return
	}
	s.attributeText(rest, spaces, end)
}

func (s *scanner) attributeText(rest []byte, spaces, end int) {
	switch {
	case len(rest) > 0 && rest[0] == '"':
		s.argument, s.mode = s.at+spaces, "string"
	case len(rest) > 0 && rest[0] == '$':
		s.argument, s.mode = s.at+spaces, "string_kv"
	default:
		length := indexAny(s.src[s.at:end], ",")
		s.raw("STR", s.at, s.at+length)
		return
	}
	s.at += spaces + 1
}

func (s *scanner) quoted() {
	end := len(s.src)
	i := bytes.IndexByte(s.src[s.at:end], '"')
	if i < 0 {
		s.at = end
		return
	}
	start := firstSet(s.argument, s.at)
	s.emit("STR", start, s.at+i+1, s.at, s.at+i)
	s.argument = -1
	s.mode = "attribute"
}

func (s *scanner) namedKey() {
	end := len(s.src)
	i := bytes.IndexByte(s.src[s.at:end], '=')
	if i < 0 {
		s.at = end
		return
	}
	start := firstSet(s.argument, s.at)
	s.emit("STR_KEY", start, s.at+i, s.at, s.at+i)
	s.mode = "string_kv_key"
}

func (s *scanner) namedEquals() {
	end := len(s.src)
	b := s.src[s.at:end]
	if len(b) == 0 || b[0] != '=' {
		return
	}
	rest := b[1:]
	spaces := 0
	for spaces < len(rest) && rest[spaces] == ' ' {
		spaces++
	}
	if spaces >= len(rest) || rest[spaces] != '"' {
		return
	}
	s.at += spaces + 2
	s.mode = "string_kv_value"
}

func (s *scanner) namedValue() {
	end := len(s.src)
	i := bytes.IndexByte(s.src[s.at:end], '"')
	if i < 0 {
		s.at = end
		return
	}
	if i > 0 {
		s.emit("STR_VALUE", s.at, s.at+i+1, s.at, s.at+i)
	} else {
		s.at++
	}
	s.argument = -1
	s.mode = "attribute"
}

func (s *scanner) lineValue() {
	end := len(s.src)
	kind := "acc_descr_value"
	if s.mode == "acc_title" {
		kind = "acc_title_value"
	}
	length := lineLen(s.src[s.at:end])
	s.raw(kind, s.at, s.at+length)
	s.mode = "INITIAL"
}

func (s *scanner) descriptionBlock() {
	end := len(s.src)
	i := bytes.IndexByte(s.src[s.at:end], '}')
	if i < 0 {
		s.at = end
		return
	}
	start := firstSet(s.argument, s.at)
	s.emit("acc_descr_multiline_value", start, s.at+i+1, s.at, s.at+i)
	s.argument = -1
	s.opening = -1
	s.mode = "INITIAL"
}

func (s *scanner) prefix(name string, end int) ([]byte, bool) {
	b := s.src[s.at:end]
	if bytes.HasPrefix(b, []byte(name)) {
		return b[len(name):], true
	}
	return nil, false
}

func directionKind(b []byte) (string, bool) {
	switch {
	case hasDirectionAxis(b, "TB"):
		return "direction_tb", true
	case hasDirectionAxis(b, "BT"):
		return "direction_bt", true
	case hasDirectionAxis(b, "RL"):
		return "direction_rl", true
	case hasDirectionAxis(b, "LR"):
		return "direction_lr", true
	}
	return "", false
}

func hasDirectionAxis(b []byte, axis string) bool {
	for at := 0; ; {
		i := bytes.Index(b[at:], []byte("direction"))
		if i < 0 {
			return false
		}
		rest := b[at+i+len("direction"):]
		value := trimLeftSpace(rest)
		if len(value) < len(rest) && hasPrefix(value, axis) {
			return true
		}
		at += i + len("direction")
	}
}

func lineLen(b []byte) int {
	if i := indexAny(b, "\r\n"); i >= 0 {
		return i
	}
	return len(b)
}

func indexAny(b []byte, chars string) int {
	if i := bytes.IndexAny(b, chars); i >= 0 {
		return i
	}
	return len(b)
}

func indexWhitespaceOrBrace(b []byte) int {
	for i := 0; i < len(b); {
		r, size := utf8.DecodeRune(b[i:])
		if unicode.IsSpace(r) || r == '{' || r == '}' {
			return i
		}
		i += size
	}
	return len(b)
}

func trimLeftSpace(b []byte) []byte {
	for len(b) > 0 {
		r, size := utf8.DecodeRune(b)
		if !unicode.IsSpace(r) {
			return b
		}
		b = b[size:]
	}
	return b
}

func startsWithSpace(b []byte) bool {
	if len(b) == 0 {
		return false
	}
	r, _ := utf8.DecodeRune(b)
	return unicode.IsSpace(r)
}

func headerBoundary(b []byte) bool {
	if len(b) == 0 {
		return false
	}
	r, _ := utf8.DecodeRune(b)
	return r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9' || r == '-' || r == '_'
}

func runeLen(b []byte) int {
	if len(b) == 0 {
		return 1
	}
	_, size := utf8.DecodeRune(b)
	if size <= 0 {
		return 1
	}
	return size
}
