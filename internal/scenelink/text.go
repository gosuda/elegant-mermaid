package scenelink

import (
	"iter"
	"sort"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	OpMoveTo uint8 = iota
	OpLineTo
	OpQuadTo
	OpCubeTo
)

func (f Font) Glyph(cp rune) Glyph {
	i := sort.Search(len(f.Glyphs), func(i int) bool { return f.Glyphs[i].Rune >= cp })
	if i < len(f.Glyphs) && f.Glyphs[i].Rune == cp {
		return f.Glyphs[i]
	}
	return Glyph{Rune: cp, Advance: fallbackAdvance(f.UnitsPerEm, cp)}
}

func fallbackAdvance(upem int32, cp rune) int32 {
	i := sort.Search(len(gen.UnicodeWidth), func(i int) bool { return gen.UnicodeWidth[i].Hi >= uint32(cp) })
	if i < len(gen.UnicodeWidth) && gen.UnicodeWidth[i].Lo <= uint32(cp) && gen.UnicodeWidth[i].Value == 2 {
		return upem
	}
	return (6*upem + 5) / 10
}

func weight(t *scene.Text, run scene.Run) int {
	if run.Bold {
		return 1
	}
	if run.Italic || t.Role == scene.TextRoleBody {
		return 0
	}
	return 1
}

func round(a, b int64) int64 { return geom.FloorDiv(2*a+b, 2*b) }

func lineHeight(t *scene.Text) int64 {
	if t.Role == scene.TextRoleTitle {
		return 1536
	}
	return 1280
}

func Baseline(t *scene.Text, line int) int64 {
	lh := lineHeight(t)
	return int64(t.Rect.Y) + int64(line)*lh + lh/2 + int64(t.Size)*64*35/100
}

func TextLeft(t *scene.Text, lineWidth int64) int64 {
	x := int64(t.Rect.X)
	switch t.Align {
	case scene.AlignMiddle:
		return x + int64(t.Rect.W)/2 - lineWidth/2
	case scene.AlignEnd:
		return x + int64(t.Rect.W) - lineWidth
	default:
		return x
	}
}

func (o Outlines) LineWidth(t *scene.Text, line []scene.Run) int64 {
	var total int64
	for _, run := range line {
		f := o[weight(t, run)]
		var sum int64
		for _, cp := range run.Text {
			sum += int64(f.Glyph(cp).Advance)
		}
		total += (sum*int64(t.Size)*64 + int64(f.UnitsPerEm) - 1) / int64(f.UnitsPerEm)
	}
	return total
}

type Placement struct {
	UnitsPerEm, Size int32
	X, Y             int64
	Italic           bool
}

func (p Placement) Point(gx, gy int32) (int64, int64) {
	h := round(int64(gy)*int64(p.Size)*64, int64(p.UnitsPerEm))
	x := p.X + round(int64(gx)*int64(p.Size)*64, int64(p.UnitsPerEm))
	if p.Italic {
		x += geom.FloorDiv(13*h, 64)
	}
	return x, p.Y - h
}

func (o Outlines) Glyphs(t *scene.Text, line []scene.Run, x, y int64) iter.Seq2[Glyph, Placement] {
	return func(yield func(Glyph, Placement) bool) {
		for _, run := range line {
			f := o[weight(t, run)]
			em := int64(f.UnitsPerEm)
			var prefix int64
			for _, cp := range run.Text {
				g := f.Glyph(cp)
				at := Placement{UnitsPerEm: f.UnitsPerEm, Size: t.Size, X: x + round(prefix*int64(t.Size)*64, em), Y: y, Italic: run.Italic}
				if !yield(g, at) {
					return
				}
				prefix += int64(g.Advance)
			}
			x += round(prefix*int64(t.Size)*64, em)
		}
	}
}
