package kanban

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	headerWord = "kanban"
	iconOpener = "::icon("
	dataOpener = "@{"
	lineBreak  = "<br/>"
)

const (
	kindSpaceLine    = "SPACELINE"
	kindKanban       = "KANBAN"
	kindClass        = "CLASS"
	kindIcon         = "ICON"
	kindNL           = "NL"
	kindNodeStart    = "NODE_DSTART"
	kindSpaceList    = "SPACELIST"
	kindNodeID       = "NODE_ID"
	kindEOF          = "EOF"
	kindNodeDescr    = "NODE_DESCR"
	kindNodeEnd      = "NODE_DEND"
	kindShapeData    = "SHAPE_DATA"
	kindInvalid      = "INVALID"
	kindUnterminated = "UNTERMINATED"
	kindEnd          = "END"
)

type mode uint8

const (
	modeInitial mode = iota
	modeNode
	modeString
	modeMarkdown
	modeIcon
	modeClass
	modeData
	modeDataString
)

type frame struct {
	mode   mode
	opener int
	text   string
}

var (
	nodeOpeners = []string{"-)", "(-", "))", ")", "((", "{{", "(", "["}
	nodeClosers = []string{"))", ")", "]", "}}", "(-", "-)", "((", "("}
)

type scanner struct {
	text     string
	orig     []int
	end      int
	at       int
	frames   []frame
	eofSent  bool
	crossed  bool
	pending  *Token
	closedAt int
}

func newScanner(src string, removed []source.Span) *scanner {
	filtered, orig := filterRemoved(src, removed)
	start := 0
	for start < len(filtered) {
		r, n := unit(filtered, start)
		if !isSpace(r) {
			break
		}
		start += n
	}
	return &scanner{text: filtered[start:] + "\n", orig: orig[start:], end: len(src), frames: []frame{{mode: modeInitial}}}
}

func filterRemoved(src string, removed []source.Span) (string, []int) {
	var text strings.Builder
	orig := make([]int, 0, len(src))
	at := 0
	for _, span := range removed {
		from, to := max(span.Start, at), min(span.End, len(src))
		if from >= to {
			continue
		}
		for i := at; i < from; i++ {
			orig = append(orig, i)
		}
		text.WriteString(src[at:from])
		at = to
	}
	for i := at; i < len(src); i++ {
		orig = append(orig, i)
	}
	text.WriteString(src[at:])
	return text.String(), orig
}

func unit(text string, at int) (rune, int) {
	c := text[at]
	switch {
	case c == '\r':
		if at+1 < len(text) && text[at+1] == '\n' {
			return '\n', 2
		}
		return '\n', 1
	case c < utf8.RuneSelf:
		return rune(c), 1
	}
	return utf8.DecodeRuneInString(text[at:])
}

func isSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func isNewline(r rune) bool { return r == '\n' }

func isDot(r rune) bool { return r != '\n' && r != 0x2028 && r != 0x2029 }

func isIDChar(r rune) bool {
	switch r {
	case '(', '[', '\n', ')', '{', '}', '@':
		return false
	}
	return true
}

func isDescrChar(r rune) bool {
	switch r {
	case ')', ']', '(', '}':
		return false
	}
	return true
}

func isDataChar(r rune) bool { return r != '}' && r != '^' && r != '"' }

func isWordByte(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func (s *scanner) mode() mode { return s.frames[len(s.frames)-1].mode }

func (s *scanner) top() frame { return s.frames[len(s.frames)-1] }

func (s *scanner) push(m mode, opener int, text string) {
	s.frames = append(s.frames, frame{mode: m, opener: opener, text: text})
}

func (s *scanner) pop() {
	if len(s.frames) > 1 {
		s.frames = s.frames[:len(s.frames)-1]
	}
}

func (s *scanner) reset() { s.frames = s.frames[:1] }

func (s *scanner) start(at int) int {
	if at >= len(s.orig) {
		return s.end
	}
	return s.orig[at]
}

func (s *scanner) finish(at int) int {
	if at <= 0 {
		return s.start(0)
	}
	if at > len(s.orig) {
		return s.end
	}
	return s.orig[at-1] + 1
}

func (s *scanner) span(from, to int) source.Span {
	return source.Span{Start: s.start(from), End: max(s.finish(to), s.start(from))}
}

func (s *scanner) token(kind string, from, to int) Token {
	s.at = to
	return Token{Kind: kind, Text: s.text[from:to], Span: s.span(from, to)}
}

func (s *scanner) run(at int, keep func(rune) bool) int {
	for at < len(s.text) {
		r, n := unit(s.text, at)
		if !keep(r) {
			break
		}
		at += n
	}
	return at
}

func (s *scanner) fold(at int, word string) bool {
	if at+len(word) > len(s.text) {
		return false
	}
	for i := range len(word) {
		c := s.text[at+i]
		if c >= 'A' && c <= 'Z' {
			c += 'a' - 'A'
		}
		if c != word[i] {
			return false
		}
	}
	return true
}

func (s *scanner) next() Token {
	if s.pending != nil {
		token := *s.pending
		s.pending = nil
		return token
	}
	for {
		if token, ok := s.step(); ok {
			return token
		}
	}
}

func (s *scanner) step() (Token, bool) {
	if s.at >= len(s.text) {
		return s.finishInput()
	}
	switch s.mode() {
	case modeNode:
		return s.node()
	case modeString:
		return s.quoted()
	case modeMarkdown:
		return s.markdown()
	case modeIcon:
		return s.icon()
	case modeClass:
		return s.class()
	case modeData:
		return s.data()
	case modeDataString:
		return s.dataString()
	}
	return s.initial()
}

func (s *scanner) finishInput() (Token, bool) {
	zero := source.Span{Start: s.end, End: s.end}
	switch s.mode() {
	case modeInitial:
		if !s.eofSent {
			s.eofSent = true
			return Token{Kind: kindEOF, Span: zero}, true
		}
		return Token{Kind: kindEnd, Span: zero}, true
	case modeClass:
		s.pop()
		return Token{}, false
	}
	open := s.top()
	s.reset()
	s.eofSent = true
	return Token{Kind: kindUnterminated, Text: open.text, Span: source.Span{Start: s.start(open.opener), End: s.end}}, true
}

func (s *scanner) descr(from, to int, quote Description) Token {
	token := s.token(kindNodeDescr, from, to)
	token.Quote = quote
	return token
}

func (s *scanner) invalid() (Token, bool) {
	_, n := unit(s.text, s.at)
	return s.token(kindInvalid, s.at, s.at+n), true
}

func (s *scanner) commentEnd(at int) (int, bool) {
	j := s.run(at, isSpace)
	if !strings.HasPrefix(s.text[j:], "%%") {
		return 0, false
	}
	return s.run(j+2, isDot), true
}

func (s *scanner) spaceLineEnd(at int) (int, bool) {
	last := -1
	for j := at; j < len(s.text); {
		r, n := unit(s.text, j)
		if !isSpace(r) {
			break
		}
		if r == '\n' && j > at {
			last = j + n
		}
		j += n
	}
	return last, last >= 0
}

func (s *scanner) headerAt(at int) bool {
	end := at + len(headerWord)
	if !s.fold(at, headerWord) {
		return false
	}
	return end >= len(s.text) || !isWordByte(s.text[end])
}

func (s *scanner) initial() (Token, bool) {
	at := s.at
	if strings.HasPrefix(s.text[at:], dataOpener) {
		s.push(modeData, at, dataOpener)
		token := s.token(kindShapeData, at, at+len(dataOpener))
		token.Text = ""
		return token, true
	}
	if end, ok := s.commentEnd(at); ok {
		return s.token(kindSpaceLine, at, end), true
	}
	if s.headerAt(at) {
		return s.token(kindKanban, at, at+len(headerWord)), true
	}
	if strings.HasPrefix(s.text[at:], ":::") {
		s.push(modeClass, at, ":::")
		s.at = at + 3
		return Token{}, false
	}
	if s.fold(at, iconOpener) {
		s.push(modeIcon, at, s.text[at:at+len(iconOpener)])
		s.at = at + len(iconOpener)
		return Token{}, false
	}
	return s.initialLines(at)
}

func (s *scanner) initialLines(at int) (Token, bool) {
	if end, ok := s.spaceLineEnd(at); ok {
		s.crossed = true
		return s.token(kindSpaceLine, at, end), true
	}
	if end := s.run(at, isNewline); end > at {
		s.crossed = true
		return s.token(kindNL, at, end), true
	}
	for _, opener := range nodeOpeners {
		if strings.HasPrefix(s.text[at:], opener) {
			s.push(modeNode, at, opener)
			return s.token(kindNodeStart, at, at+len(opener)), true
		}
	}
	if end := s.run(at, isSpace); end > at {
		return s.token(kindSpaceList, at, end), true
	}
	if end := s.run(at, isIDChar); end > at {
		return s.token(kindNodeID, at, end), true
	}
	return s.invalid()
}

func (s *scanner) node() (Token, bool) {
	at := s.at
	rest := s.text[at:]
	switch {
	case strings.HasPrefix(rest, "\"`"):
		s.push(modeMarkdown, at, "\"`")
		s.at = at + 2
		return Token{}, false
	case rest[0] == '"':
		s.push(modeString, at, "\"")
		s.at = at + 1
		return Token{}, false
	}
	for _, closer := range nodeClosers {
		if strings.HasPrefix(rest, closer) {
			s.pop()
			return s.token(kindNodeEnd, at, at+len(closer)), true
		}
	}
	if end := s.run(at, isDescrChar); end > at {
		return s.descr(at, end, DescriptionPlain), true
	}
	if end := s.run(at, isDot); end > at {
		return s.descr(at, end, DescriptionPlain), true
	}
	return s.invalid()
}

func (s *scanner) quoted() (Token, bool) {
	at := s.at
	if s.text[at] == '"' {
		s.pop()
		s.at = at + 1
		return Token{}, false
	}
	end := s.run(at, func(r rune) bool { return r != '"' })
	return s.descr(at, end, DescriptionQuoted), true
}

func (s *scanner) markdown() (Token, bool) {
	at := s.at
	if strings.HasPrefix(s.text[at:], "`\"") {
		s.pop()
		s.at = at + 2
		return Token{}, false
	}
	if end := s.run(at, func(r rune) bool { return r != '`' && r != '"' }); end > at {
		return s.descr(at, end, DescriptionMarkdown), true
	}
	return s.invalid()
}

func (s *scanner) icon() (Token, bool) {
	at := s.at
	if s.text[at] == ')' {
		s.pop()
		s.at = at + 1
		return Token{}, false
	}
	end := s.run(at, func(r rune) bool { return r != ')' })
	closed := end
	if end < len(s.text) {
		closed = end + 1
	}
	token := Token{Kind: kindIcon, Text: s.text[at:end], Span: s.span(s.top().opener, closed)}
	s.at = end
	return token, true
}

func (s *scanner) class() (Token, bool) {
	at := s.at
	if r, n := unit(s.text, at); isNewline(r) {
		s.crossed = true
		s.pop()
		s.at = at + n
		return Token{}, false
	}
	end := s.run(at, isDot)
	if end == at {
		return s.invalid()
	}
	opener := s.top().opener
	s.pop()
	token := Token{Kind: kindClass, Text: s.text[at:end], Span: s.span(opener, end)}
	s.at = end
	return token, true
}

func (s *scanner) data() (Token, bool) {
	at := s.at
	switch s.text[at] {
	case '}':
		s.pop()
		s.at = at + 1
		s.closedAt = s.finish(at + 1)
		return Token{}, false
	case '"':
		open := s.top()
		s.push(modeDataString, open.opener, open.text)
		return s.token(kindShapeData, at, at+1), true
	}
	if end := s.run(at, isDataChar); end > at {
		return s.token(kindShapeData, at, end), true
	}
	return s.invalid()
}

func (s *scanner) dataString() (Token, bool) {
	at := s.at
	if s.text[at] == '"' {
		s.pop()
		return s.token(kindShapeData, at, at+1), true
	}
	end := s.run(at, func(r rune) bool { return r != '"' })
	token := s.token(kindShapeData, at, end)
	token.Text = foldBreaks(token.Text)
	return token, true
}

func foldBreaks(text string) string {
	var out strings.Builder
	for i := 0; i < len(text); {
		r, n := unit(text, i)
		i += n
		if r != '\n' {
			out.WriteString(text[i-n : i])
			continue
		}
		out.WriteString(lineBreak)
		for i < len(text) {
			next, width := unit(text, i)
			if !isSpace(next) {
				break
			}
			i += width
		}
	}
	return out.String()
}

func isSeparator(kind string) bool {
	switch kind {
	case kindNL, kindSpaceLine, kindEOF, kindEnd:
		return true
	}
	return false
}

func (s *scanner) skipLine(contentEnd int) int {
	for {
		s.crossed = false
		token, ok := s.step()
		if ok {
			switch token.Kind {
			case kindEOF, kindEnd, kindUnterminated:
				s.pending = &token
				return contentEnd
			}
			if !isSeparator(token.Kind) {
				contentEnd = max(contentEnd, token.Span.End)
			}
		}
		if s.crossed {
			s.reset()
			return contentEnd
		}
	}
}
