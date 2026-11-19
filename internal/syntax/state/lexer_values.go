package state

import (
	"strings"
	"unicode"
)

func lineValueKind(mode lexMode) string {
	switch mode {
	case modeAccTitle:
		return "acc_title_value"
	case modeAccDescr:
		return "acc_descr_value"
	case modeClassDefID:
		return "CLASSDEF_STYLEOPTS"
	case modeClassStyle:
		return "STYLECLASS"
	case modeStyleDefStyles:
		return "STYLEDEF_STYLEOPTS"
	case modeStateID, modeFloatingNoteID:
		return kindID
	}
	return ""
}

func (s *scanner) modeValue(rest string, mode lexMode, line int) bool {
	if kind := lineValueKind(mode); kind != "" {
		return s.lineValue(rest, kind, line)
	}
	switch mode {
	case modeStateString:
		return s.closeQuoted(rest, '"', "STATE_DESCR")
	case modeAccDescrMultiline:
		return s.closeQuoted(rest, '}', "acc_descr_multiline_value")
	case modeScale:
		return s.scaleWidth(rest)
	case modeClass:
		return s.classTargets(rest)
	case modeClassDef:
		return s.classDefID(rest)
	case modeStyle:
		return s.styleTargets(rest)
	}
	return false
}

func (s *scanner) lineValue(rest, kind string, line int) bool {
	n := line
	if s.mode() == modeStateID {
		if i := strings.IndexByte(rest[:line], '{'); i >= 0 {
			n = i
		}
	}
	if kind == kindID {
		n = commentCut(rest[:n])
	}
	s.pop()
	if n == 0 && kind == kindID {
		s.pending = noOffset
		return false
	}
	s.raw(kind, n)
	return true
}

func (s *scanner) closeQuoted(rest string, closer byte, kind string) bool {
	if n := strings.IndexByte(rest, closer); n >= 0 {
		s.emit(kind, n+1, rest[:n])
		s.pop()
		return true
	}
	s.pending = max(s.at-1, 0)
	s.raw(kindUnterminated, len(rest))
	s.pop()
	return true
}

func (s *scanner) scaleWidth(rest string) bool {
	if n := asciiDigitsLen(rest); n > 0 {
		s.raw("WIDTH", n)
		return true
	}
	t := strings.TrimLeftFunc(rest, unicode.IsSpace)
	if !word(t, "width") {
		return false
	}
	s.at += len(rest) - len(t) + 5
	s.pop()
	return true
}

func (s *scanner) classTargets(rest string) bool {
	n := classIDsLen(rest)
	if n == 0 {
		return false
	}
	s.replace(modeClassStyle)
	s.raw("CLASSENTITY_IDS", n)
	return true
}

func (s *scanner) classDefID(rest string) bool {
	n := wordBytesLen(rest)
	ws := spaceAfter(rest, n)
	if n == 0 || ws == 0 {
		return false
	}
	kind := "CLASSDEF_ID"
	if asciiEqualFold(rest[:n], "default") {
		kind = "DEFAULT_CLASSDEF_ID"
	}
	s.replace(modeClassDefID)
	s.raw(kind, n+ws)
	return true
}

func (s *scanner) styleTargets(rest string) bool {
	n := styleIDsLen(rest)
	ws := spaceAfter(rest, n)
	if n == 0 || ws == 0 {
		return false
	}
	s.replace(modeStyleDefStyles)
	s.raw("STYLE_IDS", n+ws)
	return true
}
