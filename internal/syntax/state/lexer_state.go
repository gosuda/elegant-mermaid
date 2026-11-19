package state

import (
	"strings"
	"unicode"
)

var stereotypes = [...]literalRule{
	{"<<fork>>", "FORK"},
	{"<<join>>", "JOIN"},
	{"<<choice>>", "CHOICE"},
	{"[[fork]]", "FORK"},
	{"[[join]]", "JOIN"},
	{"[[choice]]", "CHOICE"},
}

var notePositions = [...]literalRule{{"left of", "left_of"}, {"right of", "right_of"}}

func (s *scanner) state(rest string, line int) bool {
	for _, st := range stereotypes {
		if p := findASCIILast(rest[:line], st.literal); p >= 0 {
			s.pop()
			s.emit(st.kind, p+len(st.literal), strings.TrimSpace(rest[:p]))
			return true
		}
	}
	if strings.HasPrefix(rest, `"`) {
		s.opening = s.at
		if s.pending == noOffset {
			s.pending = s.at
		}
		s.at++
		s.push(modeStateString)
		return true
	}
	if s.stateAlias(rest) {
		return true
	}
	if p := strings.IndexByte(rest[:line], '{'); p >= 0 && multiwordName(rest[:p]) {
		s.emit("MULTIWORD", p+1, strings.TrimSpace(rest[:p+1]))
		return true
	}
	if n := runesLen(rest, isCompositeRune); n > 0 {
		s.raw("COMPOSIT_STATE", n)
		return true
	}
	return false
}

func (s *scanner) stateAlias(rest string) bool {
	t := strings.TrimLeftFunc(rest, unicode.IsSpace)
	if !word(t, "as") {
		return false
	}
	ws := spaceAfter(t, 2)
	if ws == 0 {
		return false
	}
	s.push(modeStateID)
	s.raw("AS", len(rest)-len(t)+2+ws)
	return true
}

func (s *scanner) note(rest string, mode lexMode) bool {
	switch mode {
	case modeNote:
		return s.notePosition(rest)
	case modeNoteID:
		return s.noteTarget(rest)
	case modeNoteText:
		return s.noteText(rest)
	case modeFloatingNote:
		return s.floatingNote(rest)
	}
	return false
}

func (s *scanner) notePosition(rest string) bool {
	for _, np := range notePositions {
		if word(rest, np.literal) {
			s.replace(modeNoteID)
			s.raw(np.kind, len(np.literal))
			return true
		}
	}
	if !strings.HasPrefix(rest, `"`) {
		return false
	}
	s.pending = s.at
	s.opening = s.at
	s.at++
	s.replace(modeFloatingNote)
	return true
}

func (s *scanner) noteTarget(rest string) bool {
	text := strings.TrimLeftFunc(rest, unicode.IsSpace)
	prefix := len(rest) - len(text)
	n := commentCut(text[:runesLen(text, isNoteTargetRune)])
	if n == 0 {
		return false
	}
	s.replace(modeNoteText)
	s.emit(kindID, prefix+n, text[:n])
	return true
}

func (s *scanner) noteText(rest string) bool {
	if s.inlineNoteText(rest) {
		return true
	}
	if end, valueEnd, ok := noteEnd(rest); ok {
		s.pop()
		s.emit("NOTE_TEXT", end, strings.TrimSpace(rest[:valueEnd]))
		return true
	}
	s.raw(kindUnterminated, len(rest))
	s.pop()
	return true
}

func (s *scanner) inlineNoteText(rest string) bool {
	t := strings.TrimLeftFunc(rest, unicode.IsSpace)
	value, ok := strings.CutPrefix(t, ":")
	if !ok {
		return false
	}
	n := len(t)
	if i := strings.IndexAny(value, ":\r\n;"); i >= 0 {
		n = i + 1
	}
	if n <= 1 {
		return false
	}
	s.pop()
	s.emit("NOTE_TEXT", len(rest)-len(t)+n, strings.TrimSpace(value[:n-1]))
	return true
}

func (s *scanner) floatingNote(rest string) bool {
	t := strings.TrimLeftFunc(rest, unicode.IsSpace)
	if word(t, "as") {
		s.replace(modeFloatingNoteID)
		s.raw("AS", len(rest)-len(t)+2)
		return true
	}
	if strings.HasPrefix(rest, `"`) {
		s.at++
		return true
	}
	if n := strings.IndexByte(rest, '"'); n >= 0 {
		s.raw("NOTE_TEXT", n)
		return true
	}
	s.raw(kindUnterminated, len(rest))
	s.pop()
	return true
}
