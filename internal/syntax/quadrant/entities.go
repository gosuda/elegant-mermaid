package quadrant

import (
	"strings"
	"unicode/utf8"
)

func (s *scanner) entityEnd(at int) int {
	if s.src[at] != '#' {
		return 0
	}
	end := at + 1
	for end < len(s.src) && isWordByte(s.src[end]) {
		end++
	}
	if end == at+1 || end >= len(s.src) || s.src[end] != ';' || s.deleted[end] {
		return 0
	}
	return end + 1 - at
}

func deletedSemicolons(src string) map[int]bool {
	deleted := map[int]bool{}
	for start := 0; start < len(src); {
		end := start
		for end < len(src) && !isLineEnd(src[end:]) {
			end++
		}
		if last := strings.LastIndexByte(src[start:end], ';'); last >= 0 && annotatedLine(src[start:end], last) {
			deleted[start+last] = true
		}
		start = end + max(lineEndSize(src[end:]), 1)
	}
	return deleted
}

func isLineEnd(text string) bool { return lineEndSize(text) > 0 }

func lineEndSize(text string) int {
	if text == "" {
		return 0
	}
	r, size := utf8.DecodeRuneInString(text)
	if jsLineTerminator(r) {
		return size
	}
	return 0
}

func annotatedLine(line string, last int) bool {
	return annotated(line, "style", last) || annotated(line, "classDef", last)
}

func annotated(line, word string, last int) bool {
	from := strings.Index(line, word)
	if from < 0 {
		return false
	}
	floor := from + len(word)
	reachesHash := false
	for i := last; i > floor; {
		r, size := utf8.DecodeLastRuneInString(line[:i])
		i -= size
		switch {
		case r == '#':
			reachesHash = true
		case jsSpace(r):
			reachesHash = false
		case r == ':' && reachesHash:
			return true
		}
	}
	return false
}
