package block

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type mode uint8

const (
	modeInitial mode = iota
	modeString
	modeMDString
	modeNode
	modeBlockArrow
	modeArrowDir
	modeLinkLabel
	modeClass
	modeClassStyle
	modeClassDef
	modeClassDefID
	modeStyleStatement
	modeStyleDefinition
	modeAccTitle
	modeAccDescr
	modeAccDescrMultiline
)

type frame struct {
	mode   mode
	opener int
	text   string
}

type scanner struct {
	src     string
	removed []source.Span
	at      int
	frames  []frame
	tokens  []Token
}

var openers = []string{"-)", "(-", "))", ")", "(((", "((", "{{", "{", ">", "([", "(", "[[", "[|", "[(", ")))", "[\\", "[/", "[\\", "["}

var closers = []string{"(((", ")))", "))", "}}", "}", "(-", "-)", "((", "]]", "(", "])", "\\]", "/]", ")]", ")", "]>", "]"}

var directions = []string{"right", "left", "x", "y", "up", "down"}

func lex(src string, removed []source.Span) []Token {
	s := &scanner{src: src, removed: removed, frames: []frame{{mode: modeInitial}}}
	return s.run()
}

func (s *scanner) run() []Token {
	for s.at < len(s.src) {
		if end, ok := s.removedEnd(); ok {
			s.at = end
			continue
		}
		if !s.step() {
			s.invalid()
		}
	}
	s.finish()
	return s.tokens
}

func (s *scanner) finish() {
	end := len(s.src)
	for {
		kind, ok := remainderKinds[s.top().mode]
		if !ok {
			break
		}
		s.tokens = append(s.tokens, Token{Kind: kind, Span: source.Span{Start: end, End: end}})
		s.pop()
	}
	if top := s.top(); s.opensConstruct(top.mode) {
		s.tokens = append(s.tokens, Token{Kind: "UNTERMINATED", Text: top.text, Span: source.Span{Start: top.opener, End: end}})
	}
	s.tokens = append(s.tokens, Token{Kind: "EOF", Span: source.Span{Start: end, End: end}})
}

var remainderKinds = map[mode]string{
	modeClassStyle:      "STYLECLASS",
	modeClassDefID:      "CLASSDEF_STYLEOPTS",
	modeStyleDefinition: "STYLE_DEFINITION_DATA",
	modeAccTitle:        "acc_title_value",
	modeAccDescr:        "acc_descr_value",
}

func (s *scanner) opensConstruct(m mode) bool {
	switch m {
	case modeString, modeMDString, modeNode, modeBlockArrow, modeArrowDir, modeLinkLabel:
		return true
	}
	return false
}

func (s *scanner) removedEnd() (int, bool) {
	for _, span := range s.removed {
		if span.Start <= s.at && s.at < span.End {
			return span.End, true
		}
	}
	return 0, false
}

func (s *scanner) top() frame { return s.frames[len(s.frames)-1] }

func (s *scanner) push(m mode, opener int, text string) {
	s.frames = append(s.frames, frame{mode: m, opener: opener, text: text})
}

func (s *scanner) pop() {
	if len(s.frames) > 1 {
		s.frames = s.frames[:len(s.frames)-1]
	}
}

func (s *scanner) rest() string { return s.src[s.at:] }

func (s *scanner) emit(kind string, length int) {
	s.value(kind, length, s.src[s.at:s.at+length])
}

var paddedKinds = map[string]bool{
	"end": true, "classDef": true, "class": true, "style": true, "LINK": true, "START_LINK": true,
	"DIR": true, "BLOCK_ARROW_END": true, "acc_title": true, "acc_descr": true,
	"CLASSDEF_ID": true, "DEFAULT_CLASSDEF_ID": true,
}

func (s *scanner) value(kind string, length int, text string) {
	start, end := s.at, s.at+length
	if paddedKinds[kind] {
		raw := s.src[start:end]
		start += spaceLen(raw)
		end = start + len(strings.TrimRightFunc(raw[spaceLen(raw):], isSpace))
	}
	s.tokens = append(s.tokens, Token{Kind: kind, Text: text, Span: source.Span{Start: start, End: end}})
	s.at += length
}

func (s *scanner) invalid() {
	_, size := utf8.DecodeRuneInString(s.rest())
	s.emit("INVALID", size)
	s.frames = s.frames[:1]
}

var modeSteps = map[mode]func(*scanner) bool{
	modeString:            (*scanner).stringMode,
	modeMDString:          (*scanner).mdStringMode,
	modeNode:              (*scanner).nodeMode,
	modeBlockArrow:        (*scanner).blockArrowMode,
	modeArrowDir:          (*scanner).arrowDirMode,
	modeLinkLabel:         (*scanner).linkLabelMode,
	modeClass:             (*scanner).idListMode,
	modeStyleStatement:    (*scanner).idListMode,
	modeClassDef:          (*scanner).classDefMode,
	modeAccDescrMultiline: (*scanner).accDescrMultiline,
}

func (s *scanner) step() bool {
	current := s.top().mode
	if kind, ok := remainderKinds[current]; ok {
		return s.remainder(kind)
	}
	if step, ok := modeSteps[current]; ok {
		return step(s)
	}
	return s.initial()
}

func isSpace(r rune) bool {
	switch {
	case r >= 0x09 && r <= 0x0d, r == 0x20, r == 0xa0, r == 0x1680, r >= 0x2000 && r <= 0x200a:
		return true
	}
	switch r {
	case 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return false
}

func spaceLen(text string) int {
	n := 0
	for n < len(text) {
		r, size := utf8.DecodeRuneInString(text[n:])
		if !isSpace(r) {
			break
		}
		n += size
	}
	return n
}

func isWord(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func runLen(text string, c byte) int {
	n := 0
	for n < len(text) && text[n] == c {
		n++
	}
	return n
}

func digitLen(text string) int {
	n := 0
	for n < len(text) && isDigit(text[n]) {
		n++
	}
	return n
}

func wordLen(text string) int {
	n := 0
	for n < len(text) && isWord(text[n]) {
		n++
	}
	return n
}

func boundary(text string, n int) bool {
	return n >= len(text) || !isWord(text[n])
}

func keyword(text, word string) bool {
	return strings.HasPrefix(text, word) && boundary(text, len(word))
}

func lineLen(text string) int {
	if i := strings.IndexByte(text, '\n'); i >= 0 {
		return i
	}
	return len(text)
}

func (s *scanner) initial() bool {
	rest := s.rest()
	switch {
	case keyword(rest, "block-beta"):
		s.emit("BLOCK_DIAGRAM_KEY", len("block-beta"))
	case strings.HasPrefix(rest, "block:"):
		s.emit("id-block", len("block:"))
	case keyword(rest, "block"):
		s.emit("BLOCK_DIAGRAM_KEY", len("block"))
	default:
		return s.spaceOrColumns(rest)
	}
	return true
}

var statementScanners = []func(*scanner, string) bool{
	(*scanner).columns, (*scanner).openQuote, (*scanner).spaceBlock, (*scanner).plainKeyword,
	(*scanner).statementKeyword, (*scanner).accessibility, (*scanner).endKeyword, (*scanner).shapeOpener,
	(*scanner).nodeIdentifier, (*scanner).link, (*scanner).size,
}

func (s *scanner) spaceOrColumns(rest string) bool {
	if n := spaceLen(rest); n > 0 {
		s.at += n
		return true
	}
	for _, scan := range statementScanners {
		if scan(s, rest) {
			return true
		}
	}
	return false
}

func (s *scanner) columns(rest string) bool {
	if !strings.HasPrefix(rest, "columns") {
		return false
	}
	i := len("columns")
	gap := spaceLen(rest[i:])
	if gap == 0 {
		return false
	}
	i += gap
	if keyword(rest[i:], "auto") {
		s.value("COLUMNS", i+len("auto"), "-1")
		return true
	}
	if digits := digitLen(rest[i:]); digits > 0 {
		s.value("COLUMNS", i+digits, rest[i:i+digits])
		return true
	}
	return false
}

func (s *scanner) openQuote(rest string) bool {
	switch {
	case strings.HasPrefix(rest, "\"`"):
		s.push(modeMDString, s.at, "\"`")
		s.at += 2
	case strings.HasPrefix(rest, "\""):
		s.push(modeString, s.at, "\"")
		s.at++
	default:
		return false
	}
	return true
}

func (s *scanner) spaceBlock(rest string) bool {
	if !strings.HasPrefix(rest, "space") {
		return false
	}
	i := len("space")
	if i < len(rest) && rest[i] == ':' {
		if digits := digitLen(rest[i+1:]); digits > 0 {
			s.value("SPACE_BLOCK", i+1+digits, rest[i+1:i+1+digits])
			return true
		}
	}
	if boundary(rest, i) {
		s.value("SPACE_BLOCK", i, "1")
		return true
	}
	return false
}

func (s *scanner) plainKeyword(rest string) bool {
	for _, k := range [...]struct{ word, kind string }{{"default", "DEFAULT"}, {"linkStyle", "LINKSTYLE"}, {"interpolate", "INTERPOLATE"}} {
		if keyword(rest, k.word) {
			s.emit(k.kind, len(k.word))
			return true
		}
	}
	return false
}

func (s *scanner) statementKeyword(rest string) bool {
	for _, k := range [...]struct {
		word string
		mode mode
	}{{"classDef", modeClassDef}, {"class", modeClass}, {"style", modeStyleStatement}} {
		if !strings.HasPrefix(rest, k.word) {
			continue
		}
		if gap := spaceLen(rest[len(k.word):]); gap > 0 {
			s.push(k.mode, s.at, k.word)
			s.emit(k.word, len(k.word)+gap)
			return true
		}
	}
	return false
}

func (s *scanner) accessibility(rest string) bool {
	for _, k := range [...]struct {
		word string
		mode mode
		kind string
	}{{"accTitle", modeAccTitle, "acc_title"}, {"accDescr", modeAccDescr, "acc_descr"}} {
		if !strings.HasPrefix(rest, k.word) {
			continue
		}
		i := len(k.word) + spaceLen(rest[len(k.word):])
		if i < len(rest) && rest[i] == ':' {
			i += 1 + spaceLen(rest[i+1:])
			s.push(k.mode, s.at, k.word)
			s.emit(k.kind, i)
			return true
		}
		if k.mode == modeAccDescr && i < len(rest) && rest[i] == '{' {
			i += 1 + spaceLen(rest[i+1:])
			s.push(modeAccDescrMultiline, s.at, k.word)
			s.at += i
			return true
		}
	}
	return false
}

func (s *scanner) endKeyword(rest string) bool {
	if !keyword(rest, "end") {
		return false
	}
	s.emit("end", len("end")+spaceLen(rest[len("end"):]))
	return true
}

func (s *scanner) shapeOpener(rest string) bool {
	for _, opener := range openers {
		if strings.HasPrefix(rest, opener) {
			s.push(modeNode, s.at, opener)
			s.emit("NODE_DSTART", len(opener))
			return true
		}
	}
	if strings.HasPrefix(rest, "<[") {
		s.push(modeBlockArrow, s.at, "<[")
		s.emit("BLOCK_ARROW_START", 2)
		return true
	}
	return false
}

func nodeExcluded(r rune) bool {
	switch r {
	case '(', '[', '-', ')', '{', '}', '<', '>', ':', '=':
		return true
	}
	return isSpace(r)
}

func (s *scanner) nodeIdentifier(rest string) bool {
	n := 0
	for n < len(rest) {
		r, size := utf8.DecodeRuneInString(rest[n:])
		if nodeExcluded(r) {
			break
		}
		n += size
	}
	if n == 0 {
		return false
	}
	s.emit("NODE_ID", n)
	return true
}

func (s *scanner) size(rest string) bool {
	if len(rest) < 2 || rest[0] != ':' {
		return false
	}
	digits := digitLen(rest[1:])
	if digits == 0 {
		return false
	}
	s.value("SIZE", 1+digits, rest[1:1+digits])
	return true
}

func marker(text string, i int) int {
	if i < len(text) && strings.IndexByte("xo<", text[i]) >= 0 {
		return i + 1
	}
	return i
}

func repeatedLink(rest string, c byte) int {
	i := marker(rest, spaceLen(rest))
	run := runLen(rest[i:], c)
	if run < 2 {
		return 0
	}
	i += run
	if i < len(rest) && strings.IndexByte("xo>", rest[i]) >= 0 {
		i++
	} else if run < 3 {
		return 0
	}
	return i + spaceLen(rest[i:])
}

func dottedLink(rest string) int {
	i := marker(rest, spaceLen(rest))
	if i < len(rest) && rest[i] == '-' {
		i++
	}
	dots := runLen(rest[i:], '.')
	if dots == 0 {
		return 0
	}
	i += dots
	if i >= len(rest) || rest[i] != '-' {
		return 0
	}
	i++
	if i < len(rest) && strings.IndexByte("xo>", rest[i]) >= 0 {
		i++
	}
	return i + spaceLen(rest[i:])
}

func linkLen(rest string) int {
	for _, n := range [...]int{repeatedLink(rest, '-'), repeatedLink(rest, '='), dottedLink(rest)} {
		if n > 0 {
			return n
		}
	}
	return 0
}

func startLinkLen(rest string) int {
	i := marker(rest, spaceLen(rest))
	for _, pattern := range [...]string{"--", "==", "-."} {
		if strings.HasPrefix(rest[i:], pattern) {
			return i + 2 + spaceLen(rest[i+2:])
		}
	}
	return 0
}

func (s *scanner) link(rest string) bool {
	if n := linkLen(rest); n > 0 {
		s.emit("LINK", n)
		return true
	}
	if n := startLinkLen(rest); n > 0 {
		s.push(modeLinkLabel, s.at, strings.TrimSpace(rest[:n]))
		s.emit("START_LINK", n)
		return true
	}
	return false
}

func (s *scanner) stringMode() bool {
	rest := s.rest()
	if rest[0] == '"' {
		s.at++
		s.pop()
		return true
	}
	n := strings.IndexByte(rest, '"')
	if n < 0 {
		n = len(rest)
	}
	s.emit("STR", n)
	return true
}

func (s *scanner) mdStringMode() bool {
	rest := s.rest()
	if strings.HasPrefix(rest, "`\"") {
		s.at += 2
		s.pop()
		return true
	}
	n := 0
	for n < len(rest) && rest[n] != '`' && rest[n] != '"' {
		n++
	}
	if n == 0 {
		return false
	}
	s.emit("MD_STR", n)
	return true
}

func (s *scanner) nodeMode() bool {
	rest := s.rest()
	for _, closer := range closers {
		if strings.HasPrefix(rest, closer) {
			s.emit("NODE_DEND", len(closer))
			s.pop()
			return true
		}
	}
	return s.openQuote(rest)
}

func (s *scanner) blockArrowMode() bool {
	rest := s.rest()
	if s.openQuote(rest) {
		return true
	}
	if !strings.HasPrefix(rest, "]>") {
		return false
	}
	i := 2 + spaceLen(rest[2:])
	if i >= len(rest) || rest[i] != '(' {
		return false
	}
	s.push(modeArrowDir, s.top().opener, "<[")
	s.at += i + 1
	return true
}

func (s *scanner) arrowDirMode() bool {
	rest := s.rest()
	i := 0
	if rest[0] == ',' {
		i++
	}
	i += spaceLen(rest[i:])
	for _, name := range directions {
		if strings.HasPrefix(rest[i:], name) {
			s.at += i
			s.value("DIR", len(name)+spaceLen(rest[i+len(name):]), name)
			return true
		}
	}
	if rest[0] != ')' {
		return false
	}
	s.value("BLOCK_ARROW_END", 1+spaceLen(rest[1:]), "]>")
	s.pop()
	s.pop()
	return true
}

func (s *scanner) linkLabelMode() bool {
	rest := s.rest()
	if strings.HasPrefix(rest, "\"`") {
		s.push(modeMDString, s.at, "\"`")
		s.at += 2
		return true
	}
	if rest[0] == '"' {
		s.push(modeString, s.at, "\"")
		s.emit("LINK_LABEL", 1)
		return true
	}
	if n := linkLen(rest); n > 0 {
		s.emit("LINK", n)
		s.pop()
		return true
	}
	return false
}

func idListLen(text string) int {
	n := wordLen(text)
	if n == 0 {
		return 0
	}
	for n < len(text) && text[n] == ',' {
		next := n + 1 + spaceLen(text[n+1:])
		word := wordLen(text[next:])
		if word == 0 {
			break
		}
		n = next + word
	}
	return n
}

func (s *scanner) idListMode() bool {
	n := idListLen(s.rest())
	if n == 0 {
		return false
	}
	kind, next := "CLASSENTITY_IDS", modeClassStyle
	opener := s.top().opener
	if s.top().mode == modeStyleStatement {
		kind, next = "STYLE_ENTITY_IDS", modeStyleDefinition
	}
	s.pop()
	s.push(next, opener, "")
	s.emit(kind, n)
	return true
}

func (s *scanner) classDefMode() bool {
	kind, n := s.classDefID(s.rest())
	if n == 0 {
		return false
	}
	opener := s.top().opener
	s.pop()
	s.push(modeClassDefID, opener, "")
	s.emit(kind, n)
	return true
}

func (s *scanner) classDefID(rest string) (string, int) {
	if strings.HasPrefix(rest, "DEFAULT") {
		if gap := spaceLen(rest[len("DEFAULT"):]); gap > 0 {
			return "DEFAULT_CLASSDEF_ID", len("DEFAULT") + gap
		}
	}
	word := wordLen(rest)
	gap := spaceLen(rest[word:])
	if word == 0 || gap == 0 {
		return "", 0
	}
	return "CLASSDEF_ID", word + gap
}

func (s *scanner) remainder(kind string) bool {
	s.emit(kind, lineLen(s.rest()))
	s.pop()
	return true
}

func (s *scanner) accDescrMultiline() bool {
	rest := s.rest()
	if rest[0] == '}' {
		s.at++
		s.pop()
		return true
	}
	n := strings.IndexByte(rest, '}')
	if n < 0 {
		n = len(rest)
	}
	s.emit("acc_descr_multiline_value", n)
	return true
}
