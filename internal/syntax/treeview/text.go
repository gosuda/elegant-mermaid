package treeview

import (
	"strings"
	"unicode/utf8"
)

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', '\u00a0', '\u1680', '\u2028', '\u2029', '\u202f', '\u205f', '\u3000', '\ufeff':
		return true
	}
	return r >= '\u2000' && r <= '\u200a'
}

func lineTerminator(r rune) bool {
	return r == '\n' || r == '\r' || r == '\u2028' || r == '\u2029'
}

func trimJS(s string) string {
	return strings.TrimFunc(s, jsSpace)
}

func trimEndJS(s string) string {
	return strings.TrimRightFunc(s, jsSpace)
}

func blank(c byte) bool { return c == ' ' || c == '\t' }

func wordChar(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func collapseBlanks(s string) string {
	var b strings.Builder
	for i := 0; i < len(s); {
		if !blank(s[i]) {
			b.WriteByte(s[i])
			i++
			continue
		}
		j := i
		for j < len(s) && blank(s[j]) {
			j++
		}
		if j-i >= 2 {
			b.WriteByte(' ')
		} else {
			b.WriteString(s[i:j])
		}
		i = j
	}
	return b.String()
}

func collapseBreaks(s string) string {
	var b strings.Builder
	for i := 0; i < len(s); {
		if s[i] != '\n' && s[i] != '\r' {
			b.WriteByte(s[i])
			i++
			continue
		}
		j := i
		for j < len(s) && (s[j] == '\n' || s[j] == '\r') {
			j++
		}
		if j-i >= 2 {
			b.WriteByte('\n')
		} else {
			b.WriteString(s[i:j])
		}
		i = j
	}
	return b.String()
}

func singleLine(s string) string {
	return collapseBlanks(trimJS(s))
}

func lineRest(s string) string {
	end := strings.IndexAny(s, "\n\r")
	if end < 0 {
		return s
	}
	return s[:end]
}

func titleValue(raw string) string {
	rest := raw[strings.Index(raw, "title")+len("title"):]
	if rest == "" || !blank(rest[0]) {
		return ""
	}
	return singleLine(lineRest(rest))
}

func accTitleValue(raw string) string {
	rest := raw[strings.Index(raw, "accTitle")+len("accTitle"):]
	colon := strings.IndexByte(rest, ':')
	if colon < 0 {
		return ""
	}
	return singleLine(lineRest(rest[colon+1:]))
}

func accDescrValue(raw string) string {
	rest := raw[strings.Index(raw, "accDescr")+len("accDescr"):]
	if line := strings.TrimLeft(rest, " \t"); strings.HasPrefix(line, ":") {
		return singleLine(lineRest(line[1:]))
	}
	brace := strings.IndexByte(rest, '{')
	end := strings.IndexByte(rest[brace+1:], '}')
	return multiLine(rest[brace+1 : brace+1+end])
}

func multiLine(content string) string {
	rs := []rune(content)
	rs = stripLeadingSpace(rs)
	rs = stripTrailingSpace(rs)
	return collapseBreaks(collapseBlanks(string(rs)))
}

func atLineStart(rs []rune, i int) bool {
	return i == 0 || lineTerminator(rs[i-1])
}

func stripLeadingSpace(rs []rune) []rune {
	out := make([]rune, 0, len(rs))
	for i := 0; i < len(rs); {
		if atLineStart(rs, i) {
			j := i
			for j < len(rs) && jsSpace(rs[j]) {
				j++
			}
			if j > i {
				i = j
				continue
			}
		}
		out = append(out, rs[i])
		i++
	}
	return out
}

func stripTrailingSpace(rs []rune) []rune {
	out := make([]rune, 0, len(rs))
	for i := 0; i < len(rs); {
		if end := trailingSpaceEnd(rs, i); end > i {
			i = end
			continue
		}
		out = append(out, rs[i])
		i++
	}
	return out
}

func trailingSpaceEnd(rs []rune, i int) int {
	if !jsSpace(rs[i]) {
		return i
	}
	run := i
	for run < len(rs) && jsSpace(rs[run]) {
		run++
	}
	for k := run; k > i; k-- {
		if k == len(rs) || lineTerminator(rs[k]) {
			return k
		}
	}
	return i
}

func classValue(raw string) string {
	return trimJS(trimJS(raw)[3:])
}

func iconValue(raw string) string {
	trimmed := trimJS(raw)
	return trimmed[len("icon(") : len(trimmed)-1]
}

func descValue(raw string) string {
	return trimJS(trimJS(raw)[2:])
}

func nameValue(kind, raw string) string {
	if kind == kindQuoted {
		return raw[1 : len(raw)-1]
	}
	return strings.TrimRight(raw, " \t")
}

func utf16Len(s string) int {
	units := 0
	for _, r := range s {
		units++
		if r >= utf8.RuneSelf && r > 0xffff {
			units++
		}
	}
	return units
}
