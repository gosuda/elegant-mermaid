package main

const (
	frontmatterFence = "---"
	directiveOpen    = "%%{"
	directiveClose   = "}%%"
	commentPrefix    = "%%"
	unknownKind      = "_unknown"
	outOfScopeKind   = "_out-of-scope"
	zenumlHeader     = "zenuml"
	kindRegistryPath = "spec/data/kinds.json"
	corpusRootName   = "corpus"
	manifestName     = "MANIFEST.json"
	divergenceName   = "divergences.json"
	cacheDirName     = ".cache"
	referencesRoot   = ".references"
	refusedRoot      = "mermaid-linter"
	nameSeparator    = "~"
	manifestIndent   = "  "
)

type lineOffset struct {
	start int
	text  int
	stop  int
}

func lineOffsets(src []byte) []lineOffset {
	offsets := make([]lineOffset, 0, len(src)/24+1)
	start := 0
	for i := range src {
		if src[i] != '\n' {
			continue
		}
		offsets = append(offsets, newLineOffset(src, start, i))
		start = i + 1
	}
	if start < len(src) {
		offsets = append(offsets, newLineOffset(src, start, len(src)))
	}
	return offsets
}

func newLineOffset(src []byte, start, stop int) lineOffset {
	text := stop
	if text > start && src[text-1] == '\r' {
		text--
	}
	return lineOffset{start: start, text: text, stop: stop}
}

func (l lineOffset) content(src []byte) []byte {
	return src[l.start:l.text]
}

func (l lineOffset) raw(src []byte) []byte {
	return src[l.start:l.stop]
}

func trimSpaceTab(src []byte) []byte {
	begin, end := 0, len(src)
	for begin < end && isSpaceTabCR(src[begin]) {
		begin++
	}
	for end > begin && isSpaceTabCR(src[end-1]) {
		end--
	}
	return src[begin:end]
}

func isSpaceTabCR(c byte) bool {
	return c == ' ' || c == '\t' || c == '\r'
}

func startsWithPrefix(src []byte, prefix string) bool {
	return len(src) >= len(prefix) && string(src[:len(prefix)]) == prefix
}

func containsSubstring(src []byte, token string) bool {
	if len(src) < len(token) {
		return false
	}
	last := len(src) - len(token)
	for i := 0; i <= last; i++ {
		if string(src[i:i+len(token)]) == token {
			return true
		}
	}
	return false
}

func headerToken(src []byte) string {
	lines := lineOffsets(src)
	for i := 0; i < len(lines); i++ {
		line := trimSpaceTab(lines[i].content(src))
		switch {
		case len(line) == 0:
		case startsWithPrefix(line, directiveOpen):
			i = skipDirective(src, lines, i)
		case startsWithPrefix(line, commentPrefix):
		case string(line) == frontmatterFence:
			i = skipFrontmatter(src, lines, i)
		default:
			return leadingToken(line)
		}
	}
	return ""
}

func skipDirective(src []byte, lines []lineOffset, from int) int {
	for i := from; i < len(lines); i++ {
		if containsSubstring(lines[i].content(src), directiveClose) {
			return i
		}
	}
	return len(lines)
}

func skipFrontmatter(src []byte, lines []lineOffset, from int) int {
	for i := from + 1; i < len(lines); i++ {
		if string(trimSpaceTab(lines[i].content(src))) == frontmatterFence {
			return i
		}
	}
	return len(lines)
}

func leadingToken(line []byte) string {
	end := 0
	for end < len(line) && isTokenByte(line[end]) {
		end++
	}
	return string(line[:end])
}

func isTokenByte(c byte) bool {
	switch {
	case c >= '0' && c <= '9':
		return true
	case c >= 'a' && c <= 'z':
		return true
	case c >= 'A' && c <= 'Z':
		return true
	case c == '-' || c == '_':
		return true
	}
	return false
}

func asciiLower(s string) string {
	b := []byte(s)
	for i, c := range b {
		if c >= 'A' && c <= 'Z' {
			b[i] = c + ('a' - 'A')
		}
	}
	return string(b)
}

func inputHalf(src []byte) []byte {
	for _, line := range lineOffsets(src) {
		if string(line.content(src)) == frontmatterFence {
			return src[:line.start]
		}
	}
	return src
}
