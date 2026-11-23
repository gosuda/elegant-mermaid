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
	out := make([]byte, 0, len(fixed))
	oldAt, newAt := 0, 0
	for i, block := range before {
		oldBody := hostBodySpan(original, block)
		newBody := hostBodySpan(fixed, after[i])
		if !sameRepairedBytes(original[oldAt:oldBody.Start], fixed[newAt:newBody.Start]) {
			return nil, errHostFixBoundaries
		}
		out = append(out, original[oldAt:oldBody.Start]...)
		out = append(out, fixed[newBody.Start:newBody.End]...)
		oldAt, newAt = oldBody.End, newBody.End
	}
	if !sameRepairedBytes(original[oldAt:], fixed[newAt:]) {
		return nil, errHostFixBoundaries
	}
	return append(out, original[oldAt:]...), nil
}

func sameRepairedBytes(original, fixed []byte) bool {
	repaired, _ := source.RepairUTF8(original)
	return bytes.Equal(repaired, fixed)
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
