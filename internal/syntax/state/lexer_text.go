package state

import (
	"strings"
	"unicode"
	"unicode/utf8"
)

var directions = [...]literalRule{
	{"TB", "direction_tb"},
	{"BT", "direction_bt"},
	{"RL", "direction_rl"},
	{"LR", "direction_lr"},
}

func lineLen(s string) int {
	if i := strings.IndexAny(s, "\r\n"); i >= 0 {
		return i
	}
	return len(s)
}

func isComment(s string) bool {
	return strings.HasPrefix(s, "#") || strings.HasPrefix(s, "%%") && !strings.HasPrefix(s, "%%{")
}

func commentCut(s string) int {
	if i := strings.Index(s, "%%"); i >= 0 {
		return i
	}
	return len(s)
}

func isInlineSpace(r rune) bool {
	return r != '\r' && r != '\n' && unicode.IsSpace(r)
}

func isAtomRune(r rune) bool {
	return r != ':' && r != '-' && r != '{' && !unicode.IsSpace(r)
}

func isCompositeRune(r rune) bool {
	return r != '{' && !unicode.IsSpace(r)
}

func isNoteTargetRune(r rune) bool {
	return r != ':' && r != '-' && !unicode.IsSpace(r)
}

func startsWithSpace(s string) bool {
	r, _ := utf8.DecodeRuneInString(s)
	return unicode.IsSpace(r)
}

func spaceAfter(s string, n int) int {
	return len(s) - n - len(strings.TrimLeftFunc(s[n:], unicode.IsSpace))
}

func runesLen(s string, keep func(rune) bool) int {
	for i, r := range s {
		if !keep(r) {
			return i
		}
	}
	return len(s)
}

func runeSize(s string) int {
	_, size := utf8.DecodeRuneInString(s)
	return size
}

func isWordByte(b byte) bool {
	return b == '_' || '0' <= b && b <= '9' || 'a' <= b && b <= 'z' || 'A' <= b && b <= 'Z'
}

func startsWithWordByte(s string) bool {
	return s != "" && isWordByte(s[0])
}

func wordBytesLen(s string) int {
	n := 0
	for n < len(s) && isWordByte(s[n]) {
		n++
	}
	return n
}

func styleIDsLen(s string) int {
	n := 0
	for n < len(s) && (isWordByte(s[n]) || s[n] == ',') {
		n++
	}
	return n
}

func asciiDigitsLen(s string) int {
	n := 0
	for n < len(s) && '0' <= s[n] && s[n] <= '9' {
		n++
	}
	return n
}

func asciiLower(b byte) byte {
	if 'A' <= b && b <= 'Z' {
		return b + 'a' - 'A'
	}
	return b
}

func asciiEqualFold(a, b string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range len(a) {
		if asciiLower(a[i]) != asciiLower(b[i]) {
			return false
		}
	}
	return true
}

func word(s, w string) bool {
	return len(s) >= len(w) && asciiEqualFold(s[:len(w)], w) && !startsWithWordByte(s[len(w):])
}

func findASCIILast(s, needle string) int {
	for p := len(s) - len(needle); p >= 0; p-- {
		if asciiEqualFold(s[p:p+len(needle)], needle) {
			return p
		}
	}
	return -1
}

func direction(line string) string {
	for _, d := range directions {
		if hasDirection(line, d.literal) {
			return d.kind
		}
	}
	return ""
}

func hasDirection(line, axis string) bool {
	for p := range len(line) {
		if !word(line[p:], "direction") {
			continue
		}
		tail := line[p+9:]
		t := strings.TrimLeftFunc(tail, unicode.IsSpace)
		if len(t) < len(tail) && word(t, axis) {
			return true
		}
	}
	return false
}

func classIDsLen(s string) int {
	n := 0
	for {
		k := wordBytesLen(s[n:])
		if k == 0 {
			return n
		}
		n += k
		if !strings.HasPrefix(s[n:], ",") {
			return n
		}
		tail := strings.TrimLeftFunc(s[n+1:], unicode.IsSpace)
		if !startsWithWordByte(tail) {
			return n
		}
		n = len(s) - len(tail)
	}
}

func noteEnd(s string) (int, int, bool) {
	for p := 0; p < len(s); p++ {
		if s[p] != '\r' && s[p] != '\n' {
			continue
		}
		tail := strings.TrimLeftFunc(s[p:], unicode.IsSpace)
		if word(tail, "end note") {
			return len(s) - len(tail) + 8, p, true
		}
		p = len(s) - len(tail) - 1
	}
	return 0, 0, false
}

func multiwordName(s string) bool {
	first := wordBytesLen(s)
	if first == 0 {
		return false
	}
	tail := s[first:]
	second := strings.TrimLeftFunc(tail, unicode.IsSpace)
	return len(second) < len(tail) && startsWithWordByte(second)
}
