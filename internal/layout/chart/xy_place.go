package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *xyPlan) fit(r rect) rect {
	r.x = Clamp(r.x, 0, max(p.width-r.w, 0))
	r.y = Clamp(r.y, 0, max(p.height-r.h, 0))
	return r
}

func (p *xyPlan) place() error {
	n := len(p.specs)
	p.labelRects = make([]geom.Rect, n)
	p.labelLines = make([][]string, n)
	p.aligns = make([]scene.Align, n)
	p.shown = make([]bool, n)
	for i, s := range p.specs {
		p.labelLines[i] = []string{}
		r, align, ok := p.labelRect(i, s)
		if !ok || p.overlapsTick(i, p.fit(r)) {
			continue
		}
		g, err := p.fit(r).geom()
		if err != nil {
			return err
		}
		p.labelRects[i], p.aligns[i], p.shown[i] = g, align, true
		for _, line := range p.texts[i].lines {
			p.labelLines[i] = append(p.labelLines[i], line.Text)
		}
	}
	return p.placeBoxes()
}

func (p *xyPlan) overlapsTick(i int, r rect) bool {
	kind := p.specs[i].kind
	if !p.cell || (kind != labelXTick && kind != labelYTick) {
		return false
	}
	for j := range i {
		if p.specs[j].kind != kind || !p.shown[j] {
			continue
		}
		b := p.labelRects[j]
		if tickLabelsOverlap(r, b, p.c.edge) {
			return true
		}
	}
	return false
}

func tickLabelsOverlap(r rect, b geom.Rect, edge int64) bool {
	return r.x < int64(b.X+b.W)+edge && int64(b.X) < r.x+r.w+edge && r.y < int64(b.Y+b.H) && int64(b.Y) < r.y+r.h
}

func (p *xyPlan) insidePlot(r rect) rect {
	r.x = Clamp(r.x, p.plot.x, max(p.plot.x+p.plot.w-r.w, p.plot.x))
	r.y = Clamp(r.y, p.plot.y, max(p.plot.y+p.plot.h-r.h, p.plot.y))
	return r
}

func (p *xyPlan) labelRect(i int, s labelSpec) (rect, scene.Align, bool) {
	t := p.texts[i]
	switch s.kind {
	case labelTitle:
		return p.titleRect(t), scene.AlignMiddle, p.titleShown
	case labelXTitle:
		return p.axisTitleRect(i, &p.x)
	case labelYTitle:
		return p.axisTitleRect(i, &p.y)
	case labelXTick:
		return p.tickRect(&p.x, s.index, t)
	case labelYTick:
		return p.tickRect(&p.y, s.index, t)
	case labelLegend:
		return p.legendRect(s.plot, t)
	}
	return p.pointLabelRect(s, t)
}

func (p *xyPlan) titleRect(t textBox) rect {
	half := geom.FloorDiv(t.w, 2)
	centre := Clamp(geom.FloorDiv(2*p.plot.x+p.plot.w, 2), half, p.width-half)
	return rect{centre - half, p.c.titlePad, t.w, t.h}
}

func (p *xyPlan) axisTitleRect(i int, a *axis) (rect, scene.Align, bool) {
	t := p.texts[i]
	if a.position == posLeft {
		return rect{p.c.padX, p.titleH + p.c.axisTitlePad, t.w, t.h}, scene.AlignStart, p.sideShown && p.sideTitle == i
	}
	if a.space.title == 0 {
		return rect{}, scene.AlignMiddle, false
	}
	if a.position == posBottom {
		centre := geom.FloorDiv(a.r0+a.r1, 2)
		return rect{centre - geom.FloorDiv(t.w, 2), a.area.y + a.area.h - p.c.axisTitlePad - t.h, t.w, t.h}, scene.AlignMiddle, true
	}
	centre := a.area.x + geom.FloorDiv(a.area.w, 2)
	return rect{centre - geom.FloorDiv(t.w, 2), a.area.y + p.c.axisTitlePad, t.w, t.h}, scene.AlignMiddle, true
}

func (p *xyPlan) tickRect(a *axis, k int, t textBox) (rect, scene.Align, bool) {
	if !a.space.showLabel {
		return rect{}, scene.AlignMiddle, false
	}
	c := p.c
	pos := a.tickPosition(k, c.edge)
	line, tick := a.space.line, a.space.tick
	switch a.position {
	case posBottom:
		return rect{pos - geom.FloorDiv(t.w, 2), a.area.y + c.padY + tick + line, t.w, t.h}, scene.AlignMiddle, true
	case posLeft:
		return rect{a.area.x + a.area.w - c.padX - tick - line - t.w, pos - geom.FloorDiv(t.h, 2), t.w, t.h}, scene.AlignEnd, true
	}
	return rect{pos - geom.FloorDiv(t.w, 2), a.area.y + a.space.title + c.padY, t.w, t.h}, scene.AlignMiddle, true
}

func (p *xyPlan) legendRect(plot int, t textBox) (rect, scene.Align, bool) {
	c := p.c
	row := p.legend.y + c.legendPad + int64(plot)*(p.legendLH+c.itemGap)
	return rect{p.legend.x + c.legendPad + c.legendMarker + c.markerGap, row, t.w, t.h}, scene.AlignStart, p.legendOn
}

func (p *xyPlan) pointXY(point chartmodel.Point) (x, y int64) {
	cat := p.x.pointPosition(point, p.c.edge)
	val := p.y.valuePosition(int64(point.Value), p.c.edge)
	if p.horizontal() {
		return val, cat
	}
	return cat, val
}

func (p *xyPlan) pointLabelRect(s labelSpec, t textBox) (rect, scene.Align, bool) {
	px, py := p.pointXY(p.xy.Plots[s.plot].Points[s.index])
	if p.horizontal() {
		return p.insidePlot(rect{px + p.c.pointOffset, py - geom.FloorDiv(t.h, 2), t.w, t.h}), scene.AlignStart, true
	}
	return p.insidePlot(rect{px - geom.FloorDiv(t.w, 2), py - p.c.pointOffset - geom.FloorDiv(t.h, 2), t.w, t.h}), scene.AlignMiddle, true
}

func (p *xyPlan) barRect(point chartmodel.Point) rect {
	c := p.c
	cat := p.x.pointPosition(point, c.edge)
	val := p.y.valuePosition(int64(point.Value), c.edge)
	width := geom.FloorDiv(min(2*p.x.outer, p.x.tickDistance())*(1000-c.barPad), 1000)
	if p.cell {
		width = max(width, 1)
	}
	start := cat - geom.FloorDiv(width, 2)
	if p.horizontal() {
		return rect{p.plot.x, start, val - p.plot.x + c.edge, width}
	}
	return rect{start, val, width, p.plot.y + p.plot.h - val}
}

func (p *xyPlan) lineBounds(plot chartmodel.Plot) rect {
	var found bool
	var lo, hi struct{ x, y int64 }
	for _, point := range plot.Points {
		if !point.Present {
			continue
		}
		x, y := p.pointXY(point)
		if !found {
			lo.x, lo.y, hi.x, hi.y, found = x, y, x, y, true
			continue
		}
		lo.x, lo.y, hi.x, hi.y = min(lo.x, x), min(lo.y, y), max(hi.x, x), max(hi.y, y)
	}
	if !found {
		return rect{p.plot.x, p.plot.y, 0, 0}
	}
	return rect{lo.x, lo.y, hi.x - lo.x + p.c.edge, hi.y - lo.y + p.c.edge}
}

func (p *xyPlan) placeBoxes() error {
	p.boxRects = make([]geom.Rect, len(p.boxes))
	for i, b := range p.boxes {
		var r rect
		switch {
		case b.isPlot:
			r = p.plot
		case b.isLine:
			r = p.lineBounds(p.xy.Plots[b.plot])
		default:
			r = p.barRect(p.xy.Plots[b.plot].Points[b.point])
		}
		g, err := r.geom()
		if err != nil {
			return err
		}
		p.boxRects[i] = g
	}
	p.laidOut = true
	return nil
}
