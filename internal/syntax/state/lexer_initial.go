package state

import (
	"strings"
	"unicode"
)

type literalRule struct {
	literal string
	kind    string
}

type declarationRule struct {
	literal string
	kind    string
	mode    lexMode
}

var rootLiterals = [...]literalRule{{"click", "CLICK"}, {"href", "HREF"}, {"default", "DEFAULT"}}

var declarations = [...]declarationRule{
	{"scale", "scale", modeScale},
	{"classDef", "classDef", modeClassDef},
	{"class", "class", modeClass},
	{"style", "style", modeStyle},
	{"state", "", modeState},
	{"note", "note", modeNote},
}

var accessibilityRules = [...]declarationRule{
	{"accTitle", "acc_title", modeAccTitle},
	{"accDescr", "acc_descr", modeAccDescr},
}

var operators = [...]literalRule{{"-->", "-->"}, {"--", "CONCURRENT"}, {":::", "STYLE_SEPARATOR"}}

var headers = [...]string{"stateDiagram", "stateDiagram-v2"}

func (s *scanner) initial(rest string, line int) bool {
	if s.mode() == modeInitial && s.rootLiteral(rest) {
		return true
	}
	if kind := direction(rest[:line]); kind != "" {
		s.raw(kind, line)
		return true
	}
	if isComment(rest) {
		s.at += line
		return true
	}
	return s.declaration(rest) || s.mode() == modeInitial && s.accessibility(rest) || s.atom(rest, line)
}

func (s *scanner) rootLiteral(rest string) bool {
	for _, r := range rootLiterals {
		if word(rest, r.literal) {
			s.raw(r.kind, len(r.literal))
			return true
		}
	}
	if !strings.HasPrefix(rest, `"`) {
		return false
	}
	s.opening = s.at
	if n := strings.IndexByte(rest[1:], '"'); n >= 0 {
		s.emit("STRING", n+2, rest[1:n+1])
		return true
	}
	s.raw(kindUnterminated, len(rest))
	return true
}

func (s *scanner) declaration(rest string) bool {
	for _, d := range declarations {
		if d.mode == modeScale && s.mode() != modeInitial || !word(rest, d.literal) {
			continue
		}
		ws := spaceAfter(rest, len(d.literal))
		if ws == 0 {
			continue
		}
		s.push(d.mode)
		if d.mode == modeNote {
			s.opening = s.at
		}
		if d.kind == "" {
			s.pending = s.at
			s.at += len(d.literal) + ws
			return true
		}
		s.raw(d.kind, len(d.literal)+ws)
		return true
	}
	return false
}

func (s *scanner) accessibility(rest string) bool {
	for _, a := range accessibilityRules {
		if !word(rest, a.literal) {
			continue
		}
		tail := strings.TrimLeftFunc(rest[len(a.literal):], unicode.IsSpace)
		prefix := len(rest) - len(tail)
		if value, ok := strings.CutPrefix(tail, ":"); ok {
			s.push(a.mode)
			s.raw(a.kind, prefix+1+spaceAfter(value, 0))
			return true
		}
		if a.mode == modeAccDescr && strings.HasPrefix(tail, "{") {
			s.opening = s.at + prefix
			s.pending = s.at
			s.at += prefix + 1
			s.push(modeAccDescrMultiline)
			return true
		}
	}
	return false
}

func (s *scanner) atom(rest string, line int) bool {
	if s.mode() == modeInitial && s.rootAtom(rest) {
		return true
	}
	if strings.HasPrefix(rest, "[*]") {
		s.raw("EDGE_STATE", 3)
		return true
	}
	if n := commentCut(rest[:runesLen(rest, isAtomRune)]); n > 0 {
		s.raw(kindID, n)
		return true
	}
	if s.description(rest, line) {
		return true
	}
	return s.operator(rest)
}

func (s *scanner) rootAtom(rest string) bool {
	if s.header(rest) {
		return true
	}
	if word(rest, "hide empty description") {
		s.raw("HIDE_EMPTY", 22)
		return true
	}
	return false
}

func (s *scanner) operator(rest string) bool {
	for _, o := range operators {
		if strings.HasPrefix(rest, o.literal) && (o.kind != "CONCURRENT" || s.mode() == modeStruct) {
			s.raw(o.kind, len(o.literal))
			return true
		}
	}
	return false
}

func (s *scanner) header(rest string) bool {
	for _, h := range headers {
		if !strings.HasPrefix(rest, h) {
			continue
		}
		tail := rest[len(h):]
		if tail != "" && !startsWithSpace(tail) {
			continue
		}
		s.raw("SD", len(h)+spaceAfter(tail, 0))
		return true
	}
	return false
}

func (s *scanner) description(rest string, line int) bool {
	if !strings.HasPrefix(rest, ":") {
		return false
	}
	n := descriptionLen(rest, line)
	if n == 1 {
		return false
	}
	s.emit("DESCR", n, strings.TrimSpace(rest[:n]))
	return true
}

func descriptionLen(rest string, line int) int {
	n := 1
	for n < line && rest[n] != ';' {
		if rest[n] != ':' {
			n += runeSize(rest[n:])
			continue
		}
		if n+1 >= line || rest[n+1] == ':' || rest[n+1] == ';' {
			break
		}
		n += 1 + runeSize(rest[n+1:])
	}
	return n
}
