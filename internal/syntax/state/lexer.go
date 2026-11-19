package state

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type lexMode uint8

const (
	modeInitial lexMode = iota
	modeState
	modeStateString
	modeStateID
	modeScale
	modeAccTitle
	modeAccDescr
	modeAccDescrMultiline
	modeClassDef
	modeClassDefID
	modeClass
	modeClassStyle
	modeStyle
	modeStyleDefStyles
	modeNote
	modeNoteID
	modeNoteText
	modeFloatingNote
	modeFloatingNoteID
	modeStruct
)

const noOffset = -1

const (
	kindUnterminated = "UNTERMINATED"
	kindID           = "ID"
)

type scanner struct {
	src     string
	cleaned *source.Cleaned
	at      int
	modes   []lexMode
	tokens  []Token
	pending int
	opening int
}

func lex(src string, removed []source.Span) []Token {
	return lexCleaned(source.Clean([]byte(src), removed))
}

func lexCleaned(cleaned *source.Cleaned) []Token {
	s := &scanner{src: string(cleaned.Text), cleaned: cleaned, modes: []lexMode{modeInitial}, pending: noOffset, opening: noOffset}
	return s.run()
}

func (s *scanner) mode() lexMode {
	return s.modes[len(s.modes)-1]
}

func (s *scanner) push(m lexMode) {
	s.modes = append(s.modes, m)
}

func (s *scanner) pop() {
	s.modes = s.modes[:len(s.modes)-1]
	if len(s.modes) == 0 {
		s.modes = append(s.modes, modeInitial)
	}
}

func (s *scanner) replace(m lexMode) {
	s.pop()
	s.push(m)
}

func (s *scanner) emit(kind string, length int, value string) {
	pending := s.pending
	s.pending = noOffset
	start := pending
	if kind == kindUnterminated && s.opening != noOffset {
		start = s.opening
	}
	if start == noOffset {
		start = s.at
	}
	if kind == kindUnterminated {
		value = s.src[start : s.at+length]
	}
	s.tokens = append(s.tokens, Token{Kind: kind, Text: value, Span: source.Span{Start: start, End: s.at + length}})
	s.at += length
}

func (s *scanner) raw(kind string, length int) {
	s.emit(kind, length, s.src[s.at:s.at+length])
}

func (s *scanner) run() []Token {
	for s.at < len(s.src) {
		before, mode, count := s.at, s.mode(), len(s.tokens)
		s.next()
		if s.at == before && s.mode() == mode && len(s.tokens) == count {
			_, size := utf8.DecodeRuneInString(s.src[s.at:])
			s.raw("INVALID", size)
		}
	}
	s.finish()
	for i := range s.tokens {
		s.tokens[i].Span = s.cleaned.Span(s.tokens[i].Span.Start, s.tokens[i].Span.End)
	}
	return s.tokens
}

func (s *scanner) finish() {
	switch s.mode() {
	case modeStateString, modeNoteText, modeFloatingNote, modeAccDescrMultiline:
		start := s.opening
		if start == noOffset {
			start = s.pending
		}
		if start == noOffset {
			start = s.at
		}
		s.tokens = append(s.tokens, Token{Kind: kindUnterminated, Text: s.src[start:], Span: source.Span{Start: start, End: s.at}})
	}
	switch s.mode() {
	case modeAccTitle, modeAccDescr, modeClassDefID, modeClassStyle, modeStyleDefStyles:
		s.modeValue("", s.mode(), 0)
	}
}

func (s *scanner) next() {
	rest := s.src[s.at:]
	mode := s.mode()
	line := lineLen(rest)
	if s.modeValue(rest, mode, line) {
		return
	}
	if s.body(rest, mode, line) {
		return
	}
	if s.note(rest, mode) {
		return
	}
	s.layout(rest, mode)
}

func (s *scanner) body(rest string, mode lexMode, line int) bool {
	if mode == modeStruct && strings.HasPrefix(rest, "}") {
		s.pop()
		s.raw("STRUCT_STOP", 1)
		return true
	}
	if (mode == modeInitial || mode == modeStruct) && s.initial(rest, line) {
		return true
	}
	return mode == modeState && s.stateBody(rest, line)
}

func (s *scanner) stateBody(rest string, line int) bool {
	if isComment(rest) {
		s.at += line
		return true
	}
	return s.state(rest, line)
}

func (s *scanner) layout(rest string, mode lexMode) {
	if rest[0] == '\r' || rest[0] == '\n' {
		s.newline(rest)
		return
	}
	if ws := len(rest) - len(strings.TrimLeftFunc(rest, isInlineSpace)); ws > 0 {
		s.at += ws
		return
	}
	if (mode == modeInitial || mode == modeState) && rest[0] == '{' {
		s.pop()
		s.push(modeStruct)
		s.raw("STRUCT_START", 1)
	}
}

func (s *scanner) newline(rest string) {
	n := 1
	if strings.HasPrefix(rest, "\r\n") {
		n = 2
	}
	for m := s.mode(); m != modeInitial && m != modeStruct; m = s.mode() {
		s.pop()
	}
	s.pending = noOffset
	s.raw("NL", n)
}
