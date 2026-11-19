package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type placed struct {
	r     rect
	align scene.Align
	ok    bool
}

func shownAt(r rect, align scene.Align) placed { return placed{r, align, true} }

func centredAt(at pt, t textBox) placed {
	return shownAt(rect{at.x - geom.FloorDiv(t.w, 2), at.y - geom.FloorDiv(t.h, 2), t.w, t.h}, scene.AlignMiddle)
}

func (p *wardleyPlan) placeLabels() error {
	n := len(p.specs)
	p.rects = make([]geom.Rect, n)
	p.lines = make([][]string, n)
	p.aligns = make([]scene.Align, n)
	p.shown = make([]bool, n)
	p.layoutBox()
	for i, s := range p.specs {
		p.lines[i] = []string{}
		if s.text == "" {
			continue
		}
		at := p.labelRect(i, s)
		if !at.ok {
			continue
		}
		if err := p.keep(i, p.fitCanvas(at.r), at.align); err != nil {
			return err
		}
	}
	return nil
}

func (p *wardleyPlan) keep(i int, r rect, align scene.Align) error {
	g, err := r.geom()
	if err != nil {
		return err
	}
	p.rects[i], p.aligns[i], p.shown[i] = g, align, true
	p.lines[i] = p.texts[i].plain()
	return nil
}

func (p *wardleyPlan) labelRect(i int, s wardleySpec) placed {
	t := p.texts[i]
	switch s.kind {
	case kindTitle, kindAxisX, kindAxisY, kindStage:
		return p.chromeLabel(s, t)
	case kindNode, kindLink, kindNote:
		return p.mapLabel(s, t)
	case kindNumber, kindAnnotation:
		return p.annotationLabel(s, t)
	}
	return p.forceLabel(s, t)
}

func (p *wardleyPlan) chromeLabel(s wardleySpec, t textBox) placed {
	centred := p.plot.x + geom.FloorDiv(p.plot.w-t.w, 2)
	switch s.kind {
	case kindTitle:
		return shownAt(rect{centred, geom.FloorDiv(p.plot.y-t.h, 2), t.w, t.h}, scene.AlignMiddle)
	case kindAxisX:
		return shownAt(rect{centred, p.axisY(), t.w, t.h}, scene.AlignMiddle)
	case kindAxisY:
		return shownAt(rect{p.plot.x, p.plot.y - t.h - p.c.axisGap, t.w, t.h}, scene.AlignStart)
	}
	return p.stageLabel(s.index, t)
}

func (p *wardleyPlan) mapLabel(s wardleySpec, t textBox) placed {
	switch s.kind {
	case kindNode:
		return p.nodeLabel(s.index, t)
	case kindLink:
		return p.linkLabel(s.index, t)
	}
	at := p.notes[s.index]
	return shownAt(rect{at.x, at.y - t.h, t.w, t.h}, scene.AlignStart)
}

func (p *wardleyPlan) annotationLabel(s wardleySpec, t textBox) placed {
	if s.kind == kindNumber {
		return centredAt(p.points[s.index], t)
	}
	return p.annotationText(s.index, t)
}

func (p *wardleyPlan) stageHeight() int64 {
	return p.textStyleFor(measure.RoleLabel, int32(p.c.axisSize/64)).lineHeight()
}

func (p *wardleyPlan) axisY() int64 {
	return p.plot.y + p.plot.h + 2*p.c.stageGap + p.stageHeight()
}

func (p *wardleyPlan) stageLabel(k int, t textBox) placed {
	start, end := p.stageSpan(k)
	return shownAt(rect{geom.FloorDiv(start+end-t.w, 2), p.plot.y + p.plot.h + p.c.stageGap, t.w, t.h}, scene.AlignMiddle)
}

func (p *wardleyPlan) reach(n WardleyNode) int64 {
	switch {
	case n.PipelineParent:
		return geom.FloorDiv(p.c.squareSize, 2)
	case !p.cell && n.Strategy != WardleyNoStrategy:
		return 2 * p.c.nodeRadius
	}
	return p.c.nodeRadius
}

func (p *wardleyPlan) offset(n WardleyNode) pt {
	if p.cell {
		return pt{geom.FloorDiv(n.OffsetX, 8), geom.FloorDiv(n.OffsetY, 16)}
	}
	return pt{n.OffsetX * 64, n.OffsetY * 64}
}

func (p *wardleyPlan) nodeLabel(k int, t textBox) placed {
	n, at := p.w.Nodes[k], p.pos[k]
	switch {
	case n.HasOffset:
		off := p.offset(n)
		return centredAt(pt{at.x + off.x, at.y + off.y}, t)
	case n.Anchor:
		return centredAt(at, t)
	}
	return shownAt(rect{at.x + p.reach(n) + p.c.labelGap, at.y - t.h, t.w, t.h}, scene.AlignStart)
}

func (p *wardleyPlan) linkLabel(k int, t textBox) placed {
	l := p.w.Links[k]
	a, b := p.pos[l.From], p.pos[l.To]
	mid := pt{geom.FloorDiv(a.x+b.x, 2), geom.FloorDiv(a.y+b.y, 2)}
	dx, dy := b.x-a.x, b.y-a.y
	gap := p.c.linkLabelGap
	switch {
	case dy == 0:
		return shownAt(rect{mid.x - geom.FloorDiv(t.w, 2), mid.y - gap - t.h, t.w, t.h}, scene.AlignMiddle)
	case dx == 0:
		return shownAt(rect{mid.x + gap, mid.y - geom.FloorDiv(t.h, 2), t.w, t.h}, scene.AlignStart)
	case (dx < 0) == (dy < 0):
		return shownAt(rect{mid.x + gap, mid.y - gap - t.h, t.w, t.h}, scene.AlignStart)
	}
	return shownAt(rect{mid.x - gap - t.w, mid.y - gap - t.h, t.w, t.h}, scene.AlignStart)
}

func (p *wardleyPlan) annotationText(k int, t textBox) placed {
	if !p.w.showsBox() {
		at := p.points[k]
		return shownAt(rect{at.x + p.c.annotationRadius + p.c.labelGap, at.y - geom.FloorDiv(t.h, 2), t.w, t.h}, scene.AlignStart)
	}
	y := p.box.y + p.c.boxPad
	for _, shown := range p.boxed {
		if shown == k {
			break
		}
		y += p.textOfAnnotation(shown).h
	}
	return shownAt(rect{p.box.x + p.c.boxPad, y, t.w, t.h}, scene.AlignStart)
}

func (p *wardleyPlan) textOfAnnotation(k int) textBox {
	for i, s := range p.specs {
		if s.kind == kindAnnotation && s.index == k {
			return p.texts[i]
		}
	}
	return textBox{}
}

func (p *wardleyPlan) forceLabel(s wardleySpec, t textBox) placed {
	r := p.accels
	if s.kind == kindDeaccelerator {
		r = p.decels
	}
	f := r[s.index]
	return shownAt(rect{f.x + geom.FloorDiv(f.w-t.w, 2), f.y + f.h + p.c.linkLabelGap, t.w, t.h}, scene.AlignMiddle)
}

func (p *wardleyPlan) layoutBox() {
	if !p.w.showsBox() {
		return
	}
	var w, h int64
	for _, k := range p.boxed {
		t := p.textOfAnnotation(k)
		w, h = max(w, t.w), h+t.h
	}
	at := p.project(p.w.Box.X, p.w.Box.Y)
	p.box = p.fitPlot(rect{at.x, at.y, w + 2*p.c.boxPad, h + 2*p.c.boxPad})
}
