package railroad

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

func collapseBlanks(s string) string {
	var b strings.Builder
	for i := 0; i < len(s); {
		if s[i] != ' ' && s[i] != '\t' {
			b.WriteByte(s[i])
			i++
			continue
		}
		j := i
		for j < len(s) && (s[j] == ' ' || s[j] == '\t') {
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

func decodeEscapes(quoted string) string {
	if len(quoted) < 2 {
		return ""
	}
	content := quoted[1 : len(quoted)-1]
	var b strings.Builder
	for i := 0; i < len(content); {
		r, size := utf8.DecodeRuneInString(content[i:])
		if r != '\\' || i+size >= len(content) {
			b.WriteString(content[i : i+size])
			i += size
			continue
		}
		i += size
		escaped, esize := utf8.DecodeRuneInString(content[i:])
		switch escaped {
		case 'n':
			b.WriteByte('\n')
		case 'r':
			b.WriteByte('\r')
		case 't':
			b.WriteByte('\t')
		default:
			b.WriteRune(escaped)
		}
		i += esize
	}
	return b.String()
}

func stripQuotes(quoted string) string {
	if len(quoted) < 2 {
		return ""
	}
	return quoted[1 : len(quoted)-1]
}

func quoted(s string) bool {
	if len(s) == 0 {
		return false
	}
	first, last := s[0], s[len(s)-1]
	return (first == '"' && last == '"') || (first == '\'' && last == '\'')
}

func singleLine(s string) string {
	return collapseBlanks(trimJS(s))
}

func metaTitle(raw string, n Notation) string {
	text := singleLine(strings.TrimPrefix(raw, "title"))
	trimmed := trimJS(text)
	if !quoted(trimmed) {
		return text
	}
	if n == ABNF {
		return stripQuotes(trimmed)
	}
	return decodeEscapes(trimmed)
}

func metaAccTitle(raw string) string {
	colon := strings.IndexByte(raw, ':')
	if colon < 0 {
		return ""
	}
	return singleLine(raw[colon+1:])
}

func metaAccDescr(raw string) string {
	rest := strings.TrimPrefix(raw, "accDescr")
	if brace := strings.TrimLeftFunc(rest, jsSpace); strings.HasPrefix(brace, "{") {
		return multiLineDescr(brace[1 : len(brace)-1])
	}
	colon := strings.IndexByte(rest, ':')
	if colon < 0 {
		return ""
	}
	return singleLine(rest[colon+1:])
}

func multiLineDescr(content string) string {
	rs := []rune(content)
	rs = stripLeadingBlankLines(rs)
	rs = stripTrailingSpace(rs)
	return collapseBreaks(collapseBlanks(string(rs)))
}

func atLineStart(rs []rune, i int) bool {
	return i == 0 || lineTerminator(rs[i-1])
}

func stripLeadingBlankLines(rs []rune) []rune {
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
