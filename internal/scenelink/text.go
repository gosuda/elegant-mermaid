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
	Slot, Natural    int64
}

func (p Placement) Point(gx, gy int32) (int64, int64) {
	if p.Slot > 0 && p.Natural > p.Slot {
		den := int64(p.UnitsPerEm) * p.Natural
		h := round(int64(gy)*int64(p.Size)*64*p.Slot, den)
		x := p.X + round(int64(gx)*int64(p.Size)*64*p.Slot, den)
		if p.Italic {
			x += geom.FloorDiv(13*h, 64)
		}
		return x, p.Y - h
	}
	h := round(int64(gy)*int64(p.Size)*64, int64(p.UnitsPerEm))
	x := p.X + round(int64(gx)*int64(p.Size)*64, int64(p.UnitsPerEm))
	if p.Italic {
		x += geom.FloorDiv(13*h, 64)
	}
	return x, p.Y - h
}

type runPlan struct {
	text     *scene.Text
	run      scene.Run
	font     Font
	emo      FallbackFace
	rest     []FallbackFace
	hasEmo   bool
	scalars  []rune
	advances []int64
	origins  []int64
	em       int64
	y        int64
}

func (o Outlines) Glyphs(t *scene.Text, line []scene.Run, x, y int64) iter.Seq2[Glyph, Placement] {
	return func(yield func(Glyph, Placement) bool) {
		for _, run := range line {
			next, ok := o.emitRun(t, run, x, y, yield)
			x = next
			if !ok {
				return
			}
		}
	}
}

func (o Outlines) emitRun(t *scene.Text, run scene.Run, x, y int64, yield func(Glyph, Placement) bool) (int64, bool) {
	plan := planRun(o, t, run, x, y)
	i := 0
	for i < len(plan.scalars) {
		g, at, next := plan.at(i)
		if !yield(g, at) {
			return plan.origins[len(plan.scalars)], false
		}
		i = next
	}
	return plan.origins[len(plan.scalars)], true
}

func planRun(o Outlines, t *scene.Text, run scene.Run, x, y int64) runPlan {
	f := o[weight(t, run)]
	s := []rune(run.Text)
	plan := runPlan{
		text:     t,
		run:      run,
		font:     f,
		scalars:  s,
		advances: lineAdvances(f, s),
		em:       int64(f.UnitsPerEm),
		y:        y,
	}
	plan.origins = lineOrigins(x, plan.advances, t.Size, plan.em)
	if len(f.Fallback) > 0 {
		plan.hasEmo = true
		plan.emo = f.Fallback[0]
		plan.rest = f.Fallback[1:]
	}
	return plan
}

func lineAdvances(f Font, s []rune) []int64 {
	res := make([]int64, len(s))
	for i, cp := range s {
		res[i] = int64(f.Glyph(cp).Advance)
	}
	return res
}

func lineOrigins(x int64, advances []int64, size int32, em int64) []int64 {
	orig := make([]int64, len(advances)+1)
	orig[0] = x
	var pref int64
	for i, adv := range advances {
		pref += adv
		orig[i+1] = x + round(pref*int64(size)*64, em)
	}
	return orig
}

func sumAdvances(advances []int64, i, k int) int64 {
	var sum int64
	for _, adv := range advances[i : i+k] {
		sum += adv
	}
	return sum
}

func (p runPlan) at(i int) (Glyph, Placement, int) {
	if g, at, next, ok := p.sequence(i); ok {
		return g, at, next
	}
	if g, at, next, ok := p.emojiPair(i); ok {
		return g, at, next
	}
	if g, at, next, ok := p.interPair(i); ok {
		return g, at, next
	}
	if g, at, ok := p.interSingle(i); ok {
		return g, at, i + 1
	}
	if g, at, ok := p.emojiSingle(i); ok {
		return g, at, i + 1
	}
	if g, at, ok := p.fallbackRest(i); ok {
		return g, at, i + 1
	}
	return p.measured(i)
}

func (p runPlan) paired(i int) bool {
	return i+1 < len(p.scalars) && p.scalars[i+1] == 0xFE0F
}

func (p runPlan) fitted(face FallbackFace, g Glyph, x0, slot int64) Placement {
	nat := sceneRound(int64(g.Advance), p.text.Size, int64(face.UnitsPerEm))
	return Placement{UnitsPerEm: face.UnitsPerEm, Size: p.text.Size, X: fittedOrigin(x0, slot, nat), Y: p.y, Italic: p.run.Italic, Slot: slot, Natural: nat}
}

func (p runPlan) fittedInter(g Glyph, x0, slot int64) Placement {
	nat := sceneRound(int64(g.Advance), p.text.Size, int64(p.font.UnitsPerEm))
	return Placement{UnitsPerEm: p.font.UnitsPerEm, Size: p.text.Size, X: fittedOrigin(x0, slot, nat), Y: p.y, Italic: p.run.Italic, Slot: slot, Natural: nat}
}

func (p runPlan) plain(x0 int64) Placement {
	return Placement{UnitsPerEm: p.font.UnitsPerEm, Size: p.text.Size, X: x0, Y: p.y, Italic: p.run.Italic}
}

func (p runPlan) sequence(i int) (Glyph, Placement, int, bool) {
	if !p.hasEmo {
		return Glyph{}, Placement{}, 0, false
	}
	k, gid, ok := findSequence(p.scalars, i)
	if !ok {
		return Glyph{}, Placement{}, 0, false
	}
	g, ok := p.emo.GlyphByID(gid)
	if !ok {
		return Glyph{}, Placement{}, 0, false
	}
	g.Rune = p.scalars[i]
	slot := sceneRound(sumAdvances(p.advances, i, k), p.text.Size, p.em)
	return g, p.fitted(p.emo, g, p.origins[i], slot), i + k, true
}

func (p runPlan) emojiPair(i int) (Glyph, Placement, int, bool) {
	if !p.hasEmo {
		return Glyph{}, Placement{}, 0, false
	}
	if !p.paired(i) {
		return Glyph{}, Placement{}, 0, false
	}
	g, ok := p.emo.GlyphByRune(p.scalars[i])
	if !ok {
		return Glyph{}, Placement{}, 0, false
	}
	slot := sceneRound(p.advances[i]+p.advances[i+1], p.text.Size, p.em)
	return g, p.fitted(p.emo, g, p.origins[i], slot), i + 2, true
}

func (p runPlan) interPair(i int) (Glyph, Placement, int, bool) {
	if !p.paired(i) {
		return Glyph{}, Placement{}, 0, false
	}
	g, ok := p.font.hasInter(p.scalars[i])
	if !ok {
		return Glyph{}, Placement{}, 0, false
	}
	slot := sceneRound(p.advances[i]+p.advances[i+1], p.text.Size, p.em)
	return g, p.fittedInter(g, p.origins[i], slot), i + 2, true
}

func (p runPlan) interSingle(i int) (Glyph, Placement, bool) {
	g, ok := p.font.hasInter(p.scalars[i])
	if !ok {
		return Glyph{}, Placement{}, false
	}
	return g, p.plain(p.origins[i]), true
}

func (p runPlan) emojiSingle(i int) (Glyph, Placement, bool) {
	if !p.hasEmo {
		return Glyph{}, Placement{}, false
	}
	if !isPresentation(p.scalars[i]) {
		return Glyph{}, Placement{}, false
	}
	g, ok := p.emo.GlyphByRune(p.scalars[i])
	if !ok {
		return Glyph{}, Placement{}, false
	}
	slot := sceneRound(p.advances[i], p.text.Size, p.em)
	return g, p.fitted(p.emo, g, p.origins[i], slot), true
}

func (p runPlan) fallbackRest(i int) (Glyph, Placement, bool) {
	for _, face := range p.rest {
		g, ok := face.GlyphByRune(p.scalars[i])
		if !ok {
			continue
		}
		slot := sceneRound(p.advances[i], p.text.Size, p.em)
		return g, p.fitted(face, g, p.origins[i], slot), true
	}
	return Glyph{}, Placement{}, false
}

func (p runPlan) measured(i int) (Glyph, Placement, int) {
	return p.font.Glyph(p.scalars[i]), p.plain(p.origins[i]), i + 1
}
