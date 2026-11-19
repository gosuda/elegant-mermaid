package sequence

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type lexMode uint8

const (
	modeInitial lexMode = iota
	modeID
	modeAlias
	modeLine
	modeConfig
	modeAccTitle
	modeAccDescr
	modeAccDescrMultiline
)

type arrowRule struct {
	pattern string
	kind    string
}

var arrows = []arrowRule{
	{"->>", "SOLID_ARROW"},
	{"<<->>", "BIDIRECTIONAL_SOLID_ARROW"},
	{"-->>", "DOTTED_ARROW"},
	{"<<-->>", "BIDIRECTIONAL_DOTTED_ARROW"},
	{"->", "SOLID_OPEN_ARROW"},
	{"-->", "DOTTED_OPEN_ARROW"},
	{"-x", "SOLID_CROSS"},
	{"--x", "DOTTED_CROSS"},
	{"-)", "SOLID_POINT"},
	{"--)", "DOTTED_POINT"},
	{"--|\\", "SOLID_ARROW_TOP_DOTTED"},
	{"--|/", "SOLID_ARROW_BOTTOM_DOTTED"},
	{"--\\\\", "STICK_ARROW_TOP_DOTTED"},
	{"--//", "STICK_ARROW_BOTTOM_DOTTED"},
	{"/|--", "SOLID_ARROW_TOP_REVERSE_DOTTED"},
	{"\\|--", "SOLID_ARROW_BOTTOM_REVERSE_DOTTED"},
	{"//--", "STICK_ARROW_TOP_REVERSE_DOTTED"},
	{"\\\\--", "STICK_ARROW_BOTTOM_REVERSE_DOTTED"},
	{"-|\\", "SOLID_ARROW_TOP"},
	{"-|/", "SOLID_ARROW_BOTTOM"},
	{"-\\\\", "STICK_ARROW_TOP"},
	{"-//", "STICK_ARROW_BOTTOM"},
	{"/|-", "SOLID_ARROW_TOP_REVERSE"},
	{"\\|-", "SOLID_ARROW_BOTTOM_REVERSE"},
	{"//-", "STICK_ARROW_TOP_REVERSE"},
	{"\\\\-", "STICK_ARROW_BOTTOM_REVERSE"},
}

var loopLookahead = []string{
	"-x", "--x", "-)", "--)", "-|\\", "-\\", "-/", "-//", "-|/", "/|-", "\\|-", "//-", "\\\\-",
	"/|-", "--|\\", "--", "()",
}

type keywordRule struct {
	pattern string
	kind    string
	push    bool
	mode    lexMode
}

var keywords = []keywordRule{
	{"loop", "loop", true, modeLine},
	{"rect", "rect", true, modeLine},
	{"opt", "opt", true, modeLine},
	{"alt", "alt", true, modeLine},
	{"else", "else", true, modeLine},
	{"par", "par", true, modeLine},
	{"par_over", "par_over", true, modeLine},
	{"and", "and", true, modeLine},
	{"critical", "critical", true, modeLine},
	{"option", "option", true, modeLine},
	{"break", "break", true, modeLine},
	{"end", "end", false, 0},
	{"left of", "left_of", false, 0},
	{"right of", "right_of", false, 0},
	{"links", "links", false, 0},
	{"link", "link", false, 0},
	{"properties", "properties", false, 0},
	{"details", "details", false, 0},
	{"over", "over", false, 0},
	{"note", "note", false, 0},
	{"activate", "activate", true, modeID},
	{"deactivate", "deactivate", true, modeID},
	{"sequencediagram", "SD", false, 0},
	{"autonumber", "autonumber", false, 0},
	{"off", "off", false, 0},
	{"box", "box", true, modeLine},
	{"participant", "participant", true, modeID},
	{"actor", "actor_kw", true, modeID},
	{"create", "create", false, 0},
	{"destroy", "destroy", true, modeID},
}

type idAfter uint8

const (
	idKeep idAfter = iota
	idAlias
	idPop
)

type scanner struct {
	src     string
	cleaned *source.Cleaned
	at      int
	opener  int
	modes   []lexMode
	tokens  []Token
}

func lex(src string, removed []source.Span) []Token {
	return lexCleaned(source.Clean([]byte(src), removed))
}

func lexCleaned(cleaned *source.Cleaned) []Token {
	s := &scanner{src: string(cleaned.Text), cleaned: cleaned, modes: []lexMode{modeInitial}}
	return s.run()
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

func fold(text string) string {
	n := min(len(text), 24)
	folded := make([]byte, n)
	for i := range n {
		c := text[i]
		if c >= 'A' && c <= 'Z' {
			c += 'a' - 'A'
		}
		folded[i] = c
	}
	return string(folded)
}

func wordByte(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func (s *scanner) mode() lexMode {
	if len(s.modes) == 0 {
		return modeInitial
	}
	return s.modes[len(s.modes)-1]
}

func (s *scanner) pop() {
	if len(s.modes) > 0 {
		s.modes = s.modes[:len(s.modes)-1]
	}
}

func (s *scanner) push(m lexMode) { s.modes = append(s.modes, m) }

func (s *scanner) rest() string { return sub(s.src, min(s.at, len(s.src)), len(s.src)) }

func (s *scanner) bytes() string { return s.src[min(s.at, len(s.src)):] }

func (s *scanner) lineLen() int {
	b := s.bytes()
	if i := strings.IndexAny(b, "\n\r"); i >= 0 {
		return i
	}
	return len(b)
}

func (s *scanner) emit(kind string, length int) {
	end := min(s.at+length, len(s.src))
	s.tokens = append(s.tokens, Token{Kind: kind, Text: sub(s.src, s.at, end), Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) value(kind string, length int, text string) {
	end := min(s.at+length, len(s.src))
	s.tokens = append(s.tokens, Token{Kind: kind, Text: text, Span: source.Span{Start: s.at, End: end}})
	s.at = end
}

func (s *scanner) run() []Token {
	for s.at < len(s.src) {
		if !s.next() {
			s.invalidByte()
		}
	}
	end := len(s.src)
	s.tokens = append(s.tokens,
		Token{Kind: "NEWLINE", Span: source.Span{Start: end, End: end}},
		Token{Kind: "EOF", Span: source.Span{Start: end, End: end}})
	for i := range s.tokens {
		s.tokens[i].Span = s.cleaned.Span(s.tokens[i].Span.Start, s.tokens[i].Span.End)
	}
	return s.tokens
}

func (s *scanner) invalidByte() {
	size := 1
	if rest := s.rest(); rest != "" {
		_, size = utf8.DecodeRuneInString(rest)
	}
	s.emit("INVALID", size)
}

func (s *scanner) next() bool {
	switch s.mode() {
	case modeAccTitle, modeAccDescr:
		s.emit("acc_value", s.lineLen())
		s.pop()
		return true
	case modeAccDescrMultiline:
		return s.accessibilityBlock()
	case modeConfig:
		return s.config()
	case modeID:
		return s.idMode()
	case modeAlias:
		return s.aliasMode()
	case modeLine:
		return s.lineMode()
	}
	return s.initialMode()
}

func (s *scanner) accessibilityBlock() bool {
	rest := s.rest()
	n := strings.IndexByte(rest, '}')
	if n < 0 {
		s.unterminated("accessibility description")
		return true
	}
	if n > 0 {
		s.emit("acc_multiline_value", n)
	}
	s.at++
	s.pop()
	return true
}

func (s *scanner) unterminated(what string) {
	end := len(s.src)
	s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: what, Span: source.Span{Start: min(s.opener, end), End: end}})
	s.at = end
}

func (s *scanner) config() bool {
	rest := s.rest()
	close := strings.IndexByte(rest, '}')
	if close < 0 {
		s.unterminated("metadata object")
		return true
	}
	if close > 0 {
		s.emit("CONFIG_CONTENT", close)
		return true
	}
	if aliasFollows(rest[1:]) {
		s.emit("CONFIG_END", 1)
		s.pop()
		s.push(modeAlias)
		return true
	}
	s.emit("CONFIG_END", 1)
	s.pop()
	s.pop()
	return true
}

func (s *scanner) idMode() bool {
	if s.spaceTab() || s.hashComment() {
		return true
	}
	if strings.HasPrefix(s.bytes(), "@{") {
		s.opener = s.at
		s.emit("CONFIG_START", 2)
		s.push(modeConfig)
		return true
	}
	rest := s.rest()
	line := s.lineLen()
	head := rest[:line]
	if n, after, ok := idActorEnd(head); ok {
		s.value("ACTOR", n, strings.Trim(head[:n], " \t"))
		switch after {
		case idAlias:
			s.push(modeAlias)
		case idPop:
			s.pop()
		}
		return true
	}
	if line > 0 {
		s.value("INVALID", line, strings.Trim(head, " \t"))
		s.pop()
		return true
	}
	s.value("INVALID", 0, "")
	s.pop()
	return true
}

func (s *scanner) aliasMode() bool {
	if s.spaceTab() || s.hashComment() {
		return true
	}
	rest := s.rest()
	if fold(sub(rest, 0, 2)) == "as" && (len(rest) <= 2 || !wordByte(rest[2])) {
		s.pop()
		s.pop()
		s.push(modeLine)
		s.emit("AS", 2)
		return true
	}
	s.pop()
	s.pop()
	s.emit("NEWLINE", 0)
	return true
}

func (s *scanner) lineMode() bool {
	if s.spaceTab() {
		return true
	}
	rest := s.rest()
	line := s.lineLen()
	stop := line
	if i := strings.IndexAny(rest[:line], "#;"); i >= 0 {
		stop = i
	}
	s.pop()
	s.value("restOfLine", stop, rest[:stop])
	return true
}

func (s *scanner) initialMode() bool {
	if s.newline() || s.spaceTab() || s.hashComment() || s.percentComment() {
		return true
	}
	if s.number() || s.keyword() || s.accessibility() {
		return true
	}
	return s.actor() || s.arrow() || s.punct()
}

func (s *scanner) newline() bool {
	b := s.bytes()
	if b == "" {
		return false
	}
	switch b[0] {
	case '\n':
		n := 1
		for n < len(b) && b[n] == '\n' {
			n++
		}
		s.emit("NEWLINE", n)
		return true
	case '\r':
		n := 1
		if len(b) > 1 && b[1] == '\n' {
			n = 2
		}
		s.emit("NEWLINE", n)
		return true
	}
	return false
}

func (s *scanner) spaceTab() bool {
	b := s.bytes()
	n := 0
	for n < len(b) && (b[n] == ' ' || b[n] == '\t') {
		n++
	}
	s.at += n
	return n > 0
}

func (s *scanner) hashComment() bool {
	if !strings.HasPrefix(s.bytes(), "#") {
		return false
	}
	s.at += s.lineLen()
	return true
}

func (s *scanner) percentComment() bool {
	b := s.bytes()
	skip := 0
	switch {
	case strings.HasPrefix(b, "%%") && (len(b) <= 2 || b[2] != '{'):
		skip = 2
	case b != "" && b[0] != '}' && len(b) >= 3 && b[1:3] == "%%":
		skip = 1
	}
	if skip == 0 {
		return false
	}
	s.at += s.lineLen()
	return true
}

func (s *scanner) number() bool {
	length, ok := numberLength(s.bytes())
	if !ok {
		return false
	}
	s.emit("NUM", length)
	return true
}

func (s *scanner) keyword() bool {
	rest := s.rest()
	folded := fold(rest)
	for _, rule := range keywords {
		if !strings.HasPrefix(folded, rule.pattern) {
			continue
		}
		length := len(rule.pattern)
		if length < len(rest) && wordByte(rest[length]) {
			continue
		}
		switch rule.kind {
		case "links", "link", "properties", "details":
			if !linkFollows(sub(rest, length, len(rest))) {
				continue
			}
		}
		s.emit(rule.kind, length)
		if rule.push {
			s.push(rule.mode)
		}
		return true
	}
	return s.keywordTitle(rest, "title", "title") || s.keywordTitle(rest, "title:", "legacy_title")
}

func (s *scanner) keywordTitle(rest, pattern, kind string) bool {
	if !strings.HasPrefix(fold(rest), pattern) {
		return false
	}
	if !spaceAt(rest, len(pattern)) {
		return false
	}
	line := s.lineLen()
	tail := sub(rest, len(pattern)+1, line)
	stop := len(tail)
	if i := strings.IndexAny(tail, "#;"); i >= 0 {
		stop = i
	}
	if stop == 0 {
		return false
	}
	s.emit(kind, len(pattern)+1+stop)
	return true
}

func (s *scanner) accessibility() bool {
	rest := s.rest()
	folded := fold(rest)
	for _, rule := range []struct {
		pattern, kind string
		mode          lexMode
	}{{"acctitle", "acc_title", modeAccTitle}, {"accdescr", "acc_descr", modeAccDescr}} {
		if !strings.HasPrefix(folded, rule.pattern) {
			continue
		}
		length, ok := accessibilityLength(rest, len(rule.pattern))
		if !ok {
			continue
		}
		s.emit(rule.kind, length)
		s.push(rule.mode)
		return true
	}
	if strings.HasPrefix(folded, "accdescr") {
		if length, ok := braceLength(rest, len("accdescr")); ok {
			s.opener = s.at
			s.at += length
			s.push(modeAccDescrMultiline)
			return true
		}
	}
	return false
}

func (s *scanner) actor() bool {
	rest := s.rest()
	head := rest[:s.lineLen()]
	end, ok := actorEnd(head)
	if !ok {
		return false
	}
	s.value("ACTOR", end, strings.Trim(head[:end], " \t"))
	return true
}

func (s *scanner) arrow() bool {
	rest := s.rest()
	for _, rule := range arrows {
		if strings.HasPrefix(rest, rule.pattern) {
			s.emit(rule.kind, len(rule.pattern))
			return true
		}
	}
	return false
}

var punctuation = map[byte]string{'+': "+", '-': "-", ',': ",", ';': "NEWLINE"}

func spaceAt(text string, at int) bool {
	return at < len(text) && (text[at] == ' ' || text[at] == '\t')
}

func (s *scanner) punct() bool {
	b := s.bytes()
	if b == "" {
		return false
	}
	if kind, ok := punctuation[b[0]]; ok {
		s.emit(kind, 1)
		return true
	}
	switch {
	case b[0] == ':':
		line := s.lineLen()
		stop := line
		if i := strings.IndexAny(b[:line], "#;"); i >= 0 {
			stop = i
		}
		s.emit("TXT", stop)
	case strings.HasPrefix(b, "()"):
		s.emit("()", 2)
	default:
		return false
	}
	return true
}

func digitRun(b string, from int) int {
	n := 0
	for from+n < len(b) && isDigit(b[from+n]) {
		n++
	}
	return n
}

func fractionLength(b string, from int) int {
	if from+1 < len(b) && b[from] == '.' && isDigit(b[from+1]) {
		return 1 + min(digitRun(b, from+1), 2)
	}
	return 0
}

func leadingNumber(b string) int {
	if whole := digitRun(b, 0); whole > 0 {
		return whole + fractionLength(b, whole)
	}
	if tail := digitRun(b, 1); strings.HasPrefix(b, ".") && tail > 0 {
		return 1 + tail
	}
	return 0
}

func numberLength(b string) (int, bool) {
	length := leadingNumber(b)
	if length == 0 || length >= len(b) {
		return 0, false
	}
	if c := b[length]; c != ' ' && c != '\n' && c != '\r' {
		return 0, false
	}
	return length, true
}

func idActorEnd(head string) (int, idAfter, bool) {
	if tight := plainIDRun(head); tight > 0 {
		if configFollows(head[tight:]) {
			return tight, idKeep, true
		}
		if aliasFollows(head[tight:]) {
			return tight, idAlias, true
		}
	}
	run := spacedIDRun(head)
	if run == 0 {
		return 0, idPop, false
	}
	if head[run:] == "" || strings.HasPrefix(head[run:], ";") {
		return run, idPop, true
	}
	if at := strings.LastIndexByte(head[:run], '#'); at > 0 {
		return at, idPop, true
	}
	return 0, idPop, false
}

func plainIDRun(head string) int {
	return runUntil(head, func(c rune) bool {
		return strings.ContainsRune("<>:,;@\r\n \t", c)
	})
}

func spacedIDRun(head string) int {
	return runUntil(head, func(c rune) bool {
		return strings.ContainsRune("<>:,;@\r\n", c)
	})
}

func runUntil(text string, stop func(rune) bool) int {
	n := 0
	for n < len(text) {
		c, size := utf8.DecodeRuneInString(text[n:])
		if stop(c) {
			break
		}
		n += size
	}
	return n
}

func actorEnd(head string) (int, bool) {
	n := runUntil(head, func(c rune) bool {
		return strings.ContainsRune("/\\+()<->:,;\r\n", c)
	})
	if n == 0 {
		return 0, false
	}
	end := n
	for end < len(head) {
		tail := head[end:]
		if arrowAhead(tail) {
			break
		}
		hyphens := 0
		for hyphens < len(tail) && tail[hyphens] == '-' {
			hyphens++
		}
		run := plainRun(tail[hyphens:])
		if run == 0 {
			break
		}
		end += hyphens + run
	}
	return end, true
}

func plainRun(text string) int {
	return runUntil(text, func(c rune) bool {
		return strings.ContainsRune("+<->:,;\r\n", c)
	})
}

func arrowAhead(text string) bool {
	for _, pattern := range loopLookahead {
		if strings.HasPrefix(text, pattern) {
			return true
		}
	}
	return false
}

func aliasFollows(text string) bool {
	index := 0
	for index < len(text) && (text[index] == ' ' || text[index] == '\t') {
		index++
	}
	if index == 0 || fold(sub(text, index, index+2)) != "as" {
		return false
	}
	if index+2 >= len(text) {
		return true
	}
	c := text[index+2]
	return c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

func configFollows(text string) bool {
	index := 0
	for index < len(text) && (text[index] == ' ' || text[index] == '\t') {
		index++
	}
	return strings.HasPrefix(text[index:], "@{")
}

func skipSpace(text string, from int) int {
	index := from
	for index < len(text) {
		switch text[index] {
		case ' ', '\t', '\n', '\r', 0x0b, 0x0c:
			index++
		default:
			return index
		}
	}
	return index
}

func accessibilityLength(rest string, from int) (int, bool) {
	index := skipSpace(rest, from)
	if index >= len(rest) || rest[index] != ':' {
		return 0, false
	}
	return skipSpace(rest, index+1), true
}

func braceLength(rest string, from int) (int, bool) {
	index := skipSpace(rest, from)
	if index >= len(rest) || rest[index] != '{' {
		return 0, false
	}
	return skipSpace(rest, index+1), true
}

func linkFollows(text string) bool {
	trimmed := strings.TrimLeft(text, " \t")
	if len(trimmed) == len(text) {
		return false
	}
	c, _ := utf8.DecodeRuneInString(trimmed)
	if trimmed == "" || isUnicodeSpace(c) {
		return false
	}
	return !strings.ContainsRune("/\\+()<>:,;-", c)
}

func isUnicodeSpace(c rune) bool {
	switch c {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0x85, 0xA0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000:
		return true
	}
	return c >= 0x2000 && c <= 0x200a
}
