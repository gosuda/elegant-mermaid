package lint

import "github.com/gosuda/elegant-mermaid/internal/source"

type line struct {
	start int
	end   int
	next  int
}

func lineAt(src []byte, pos int) line {
	end := pos
	for end < len(src) && src[end] != '\n' && src[end] != '\r' {
		end++
	}
	if end == len(src) {
		return line{start: pos, end: end, next: end}
	}
	next := end + 1
	if src[end] == '\r' && next < len(src) && src[next] == '\n' {
		next++
	}
	return line{start: pos, end: end, next: next}
}

func (l line) exclusiveEnd() int {
	if l.next > l.end {
		return l.next
	}
	return l.end + 1
}

func isBlank(b byte) bool {
	return b == ' ' || b == '\t'
}

func skipBlanks(src []byte, from, limit int) int {
	for from < limit && isBlank(src[from]) {
		from++
	}
	return from
}

func trimEnd(src []byte, from, end int) int {
	for end > from && isBlank(src[end-1]) {
		end--
	}
	return end
}

func hasPrefixAt(src []byte, at, limit int, want string) bool {
	return limit-at >= len(want) && string(src[at:at+len(want)]) == want
}

func containsOffset(spans []source.Span, at int) bool {
	for _, s := range spans {
		if at >= s.Start && at < s.End {
			return true
		}
	}
	return false
}

func foldASCII(b byte) byte {
	if b >= 'A' && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

func hasSuffixFold(s, suffix string) bool {
	if len(s) < len(suffix) {
		return false
	}
	tail := s[len(s)-len(suffix):]
	for i := range len(suffix) {
		if foldASCII(tail[i]) != suffix[i] {
			return false
		}
	}
	return true
}
