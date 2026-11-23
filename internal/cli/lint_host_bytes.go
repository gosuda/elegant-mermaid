package cli

import (
	"bytes"
	"errors"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/markdown"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

var errHostFixBoundaries = errors.New("lint fix changed Markdown block boundaries")

// preserveHostBytes transplants fixed block bodies into the original host.
// The fix engine may repair the analysis text, but protected host bytes must
// remain unchanged. Before restoring invalid host bytes, verify that each
// protected gap equals its repaired original.
func preserveHostBytes(original, fixed []byte) ([]byte, error) {
	if utf8.Valid(original) {
		return fixed, nil
	}
	before, after := markdown.Blocks(original), markdown.Blocks(fixed)
	if len(before) != len(after) {
		return nil, errHostFixBoundaries
	}
	oldBodies, newBodies := hostBodySpans(original, before), hostBodySpans(fixed, after)
	if !alignHostBodies(original, fixed, oldBodies, newBodies) {
		return nil, errHostFixBoundaries
	}
	out := make([]byte, 0, len(fixed))
	oldAt := 0
	for i, oldBody := range oldBodies {
		newBody := newBodies[i]
		out = append(out, original[oldAt:oldBody.Start]...)
		out = append(out, fixed[newBody.Start:newBody.End]...)
		oldAt = oldBody.End
	}
	return append(out, original[oldAt:]...), nil
}

func hostBodySpans(host []byte, blocks []markdown.Block) []source.Span {
	spans := make([]source.Span, len(blocks))
	for i, block := range blocks {
		spans[i] = hostBodySpan(host, block)
	}
	return spans
}

func alignHostBodies(original, fixed []byte, before, after []source.Span) bool {
	oldAt, newAt := 0, 0
	for i := 0; i <= len(before); i++ {
		oldEnd, newEnd := len(original), len(fixed)
		if i < len(before) {
			oldEnd, newEnd = before[i].Start, after[i].Start
		}
		gap, ok := matchHostGap(original[oldAt:oldEnd], fixed, source.Span{Start: newAt, End: newEnd}, i > 0, i < len(after))
		if !ok {
			return false
		}
		if i > 0 {
			after[i-1].End = gap.Start
		}
		if i < len(before) {
			after[i].Start = gap.End
			oldAt, newAt = before[i].End, after[i].End
		}
	}
	return hostBodiesOrdered(after, len(fixed))
}

func matchHostGap(original, fixed []byte, gap source.Span, hasBefore, hasAfter bool) (source.Span, bool) {
	starts, ends := hostGapCandidates(original, fixed, gap, hasBefore, hasAfter)
	repaired, _ := source.RepairUTF8(original)
	for _, start := range starts {
		for _, end := range ends {
			if start <= end && bytes.Equal(repaired, fixed[start:end]) {
				return source.Span{Start: start, End: end}, true
			}
		}
	}
	return source.Span{}, false
}

// A deletion can join a body's CR with a protected LF, or an opener's CR
// with a body's LF. Only that LF may move across a rescanned body boundary.
// Keep the unchanged boundary first; file endpoints have no adjacent body.
func hostGapCandidates(original, fixed []byte, gap source.Span, hasBefore, hasAfter bool) ([]int, []int) {
	starts, ends := []int{gap.Start}, []int{gap.End}
	if hasBefore && len(original) > 0 && original[0] == '\n' && afterCRLF(fixed, gap.Start) {
		starts = append(starts, gap.Start-1)
	}
	if hasAfter && len(original) > 0 && original[len(original)-1] == '\r' && afterCRLF(fixed, gap.End) {
		ends = append(ends, gap.End-1)
	}
	return starts, ends
}

func afterCRLF(host []byte, at int) bool {
	return at >= 2 && host[at-2] == '\r' && host[at-1] == '\n'
}

func hostBodiesOrdered(bodies []source.Span, size int) bool {
	end := 0
	for _, body := range bodies {
		if body.Start < end || body.End < body.Start || body.End > size {
			return false
		}
		end = body.End
	}
	return true
}

func hostBodySpan(host []byte, block markdown.Block) source.Span {
	if len(block.Lines) == 0 {
		at := hostLineEnd(host, block.Span.Start)
		return source.Span{Start: at, End: at}
	}
	start := block.Lines[0].HostOffset
	for start > 0 && host[start-1] != '\r' && host[start-1] != '\n' {
		start--
	}
	last := block.Lines[len(block.Lines)-1]
	return source.Span{Start: start, End: hostLineEnd(host, last.HostOffset+last.Len)}
}

func hostLineEnd(host []byte, at int) int {
	for at < len(host) && host[at] != '\r' && host[at] != '\n' {
		at++
	}
	if at < len(host) && host[at] == '\r' {
		at++
		if at < len(host) && host[at] == '\n' {
			at++
		}
	} else if at < len(host) {
		at++
	}
	return at
}
