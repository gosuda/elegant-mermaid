package treeview

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func prepare(src string, removed []source.Span) (string, []int) {
	front := syntax.Preprocess([]byte(src)).Frontmatter
	kept, origin := filterRemoved(src, structural(src, removed, front))
	kept, origin = normalizeBreaks(kept, origin)
	kept, origin = dropComments(kept, origin)
	return trimStart(kept, origin)
}

func lineBreak(c byte) bool { return c == '\n' || c == '\r' }

func lineStartAt(src string, at int) bool { return at == 0 || lineBreak(src[at-1]) }

func nextLine(src string, at int) int {
	for at < len(src) && !lineBreak(src[at]) {
		at++
	}
	if at+1 < len(src) && src[at] == '\r' && src[at+1] == '\n' {
		return at + 2
	}
	return min(at+1, len(src))
}

func commentLineText(line string) bool {
	rest := strings.TrimLeft(line, " \t")
	return strings.HasPrefix(rest, "%%") && !strings.HasPrefix(rest, "%%{")
}

func structural(src string, removed []source.Span, front source.Span) []source.Span {
	var out []source.Span
	for _, span := range removed {
		to := min(span.End, len(src))
		for pos := max(span.Start, 0); pos < to; {
			end := min(nextLine(src, pos), to)
			inFront := pos < front.End && pos >= front.Start
			if !lineStartAt(src, pos) || inFront || !commentLineText(src[pos:end]) {
				out = appendSpan(out, pos, end)
			}
			pos = end
		}
	}
	return out
}

func appendSpan(spans []source.Span, from, to int) []source.Span {
	if n := len(spans); n > 0 && spans[n-1].End == from {
		spans[n-1].End = to
		return spans
	}
	return append(spans, source.Span{Start: from, End: to})
}

func filterRemoved(src string, removed []source.Span) ([]byte, []int) {
	kept := make([]byte, 0, len(src))
	origin := make([]int, 0, len(src))
	at := 0
	for _, span := range removed {
		from, to := max(span.Start, at), min(span.End, len(src))
		if from >= to {
			continue
		}
		kept, origin = appendRange(kept, origin, src, at, from)
		at = to
	}
	return appendRange(kept, origin, src, at, len(src))
}

func appendRange(kept []byte, origin []int, src string, from, to int) ([]byte, []int) {
	for i := from; i < to; i++ {
		kept = append(kept, src[i])
		origin = append(origin, i)
	}
	return kept, origin
}

func normalizeBreaks(kept []byte, origin []int) ([]byte, []int) {
	text := make([]byte, 0, len(kept))
	mapped := make([]int, 0, len(kept))
	for i := 0; i < len(kept); i++ {
		c, at := kept[i], origin[i]
		if c == '\r' {
			c = '\n'
			if i+1 < len(kept) && kept[i+1] == '\n' {
				i++
				at = origin[i]
			}
		}
		text = append(text, c)
		mapped = append(mapped, at)
	}
	return text, mapped
}

func skipSpace(text []byte, at int) int {
	for at < len(text) {
		r, n := utf8.DecodeRune(text[at:])
		if !jsSpace(r) {
			break
		}
		at += n
	}
	return at
}

func lineEndIndex(text []byte, at int) int {
	for at < len(text) && text[at] != '\n' {
		at++
	}
	return at
}

func commentExtent(text []byte, q int) (int, bool) {
	rest := text[q:]
	if len(rest) < 2 || rest[0] != '%' || rest[1] != '%' || len(rest) > 2 && rest[2] == '{' {
		return 0, false
	}
	return min(lineEndIndex(text, q+2)+1, len(text)), true
}

func dropComments(text []byte, origin []int) ([]byte, []int) {
	out := make([]byte, 0, len(text))
	mapped := make([]int, 0, len(text))
	for p := 0; p < len(text); {
		q := skipSpace(text, p)
		if end, ok := commentExtent(text, q); ok {
			p = end
			continue
		}
		next := min(lineEndIndex(text, q)+1, len(text))
		out = append(out, text[p:next]...)
		mapped = append(mapped, origin[p:next]...)
		p = next
	}
	return out, mapped
}

func trimStart(text []byte, origin []int) (string, []int) {
	start := skipSpace(text, 0)
	return string(text[start:]), origin[start:]
}
