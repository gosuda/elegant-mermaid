package source

import (
	"cmp"
	"slices"
	"sort"
)

type Cleaned struct {
	Text     []byte
	srcLen   int
	segments []segment
}

type segment struct {
	clean  int
	orig   int
	length int
}

func Clean(src []byte, removed []Span) *Cleaned {
	gaps := mergeGaps(removed, len(src))
	c := &Cleaned{srcLen: len(src)}
	if len(gaps) == 0 {
		c.Text = src
		c.segments = []segment{{length: len(src)}}
		return c
	}
	text := make([]byte, 0, len(src))
	at := 0
	for _, gap := range gaps {
		text = c.keep(text, src, at, gap.Start)
		at = gap.End
	}
	c.Text = c.keep(text, src, at, len(src))
	return c
}

func (c *Cleaned) keep(text, src []byte, from, to int) []byte {
	if to <= from {
		return text
	}
	c.segments = append(c.segments, segment{clean: len(text), orig: from, length: to - from})
	return append(text, src[from:to]...)
}

func mergeGaps(removed []Span, limit int) []Span {
	gaps := make([]Span, 0, len(removed))
	for _, s := range removed {
		s.Start = max(0, min(s.Start, limit))
		s.End = max(s.Start, min(s.End, limit))
		if s.End > s.Start {
			gaps = append(gaps, s)
		}
	}
	slices.SortFunc(gaps, func(a, b Span) int {
		return cmp.Or(cmp.Compare(a.Start, b.Start), cmp.Compare(a.End, b.End))
	})
	out := gaps[:0]
	for _, s := range gaps {
		if n := len(out); n > 0 && s.Start <= out[n-1].End {
			out[n-1].End = max(out[n-1].End, s.End)
			continue
		}
		out = append(out, s)
	}
	return out
}

func (c *Cleaned) Offset(clean int) int {
	clean = max(clean, 0)
	if clean >= len(c.Text) {
		return c.srcLen
	}
	i := sort.Search(len(c.segments), func(i int) bool { return c.segments[i].clean > clean }) - 1
	return c.segments[i].orig + clean - c.segments[i].clean
}

func (c *Cleaned) Span(start, end int) Span {
	if end <= start {
		at := c.Offset(start)
		return Span{Start: at, End: at}
	}
	return Span{Start: c.Offset(start), End: c.Offset(end-1) + 1}
}

func (c *Cleaned) Index(orig int) int {
	i := sort.Search(len(c.segments), func(i int) bool { return c.segments[i].orig > orig }) - 1
	if i < 0 {
		return 0
	}
	s := c.segments[i]
	return s.clean + min(orig-s.orig, s.length)
}

func (c *Cleaned) Slice(span Span) []byte {
	return c.Text[c.Index(span.Start):c.Index(span.End)]
}
