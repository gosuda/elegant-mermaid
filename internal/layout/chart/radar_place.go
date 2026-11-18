package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func polar(radius int64, theta int32) point {
	return point{
		geom.FloorDiv(radius*int64(geom.CosQ15(theta)), q15One),
		geom.FloorDiv(radius*int64(geom.SinQ15(theta)), q15One),
	}
}

func (p *radarPlan) theta(j int) int32 {
	n := int64(len(p.r.Axes))
	return int32(geom.FloorMod(geom.FloorDiv(int64(j)*fullTurn, n)-quarterTurn, fullTurn))
}

func (p *radarPlan) valueRadius(v int64) int64 {
	clip := Clamp(v, p.lo, p.hi)
	return geom.FloorDiv(p.radius*(clip-p.lo), p.hi-p.lo)
}

func (p *radarPlan) vertices(radius int64) []point {
	out := make([]point, len(p.r.Axes))
	for j := range out {
		out[j] = polar(radius, p.theta(j))
	}
	return out
}

func (p *radarPlan) curvePoints(index int) []point {
	values := p.r.Curves[index].Values
	out := make([]point, len(values))
	for j, v := range values {
		out[j] = polar(p.valueRadius(int64(v)), p.theta(j))
	}
	return out
}

type bezier struct{ c1, c2, to point }

func (p *radarPlan) smooth(points []point) []bezier {
	n := len(points)
	t := p.c.tension
	out := make([]bezier, n)
	for i := range n {
		p0, p1 := points[(i+n-1)%n], points[i]
		p2, p3 := points[(i+1)%n], points[(i+2)%n]
		out[i] = bezier{
			c1: point{p1.x + geom.FloorDiv((p2.x-p0.x)*t, 1000), p1.y + geom.FloorDiv((p2.y-p0.y)*t, 1000)},
			c2: point{p2.x - geom.FloorDiv((p3.x-p1.x)*t, 1000), p2.y - geom.FloorDiv((p3.y-p1.y)*t, 1000)},
			to: p2,
		}
	}
	return out
}

func (p *radarPlan) alignOf(theta int32) scene.Align {
	cos := int64(geom.CosQ15(theta))
	switch {
	case cos >= p.c.anchor:
		return scene.AlignStart
	case cos <= -p.c.anchor:
		return scene.AlignEnd
	}
	return scene.AlignMiddle
}

func (p *radarPlan) axisRect(index int, t textBox) (rect, scene.Align) {
	theta := p.theta(index)
	cos, sin := int64(geom.CosQ15(theta)), int64(geom.SinQ15(theta))
	at := point{geom.FloorDiv((p.radius+p.c.gapX)*cos, q15One), geom.FloorDiv((p.radius+p.c.gapY)*sin, q15One)}
	align := p.alignOf(theta)
	x := at.x - geom.FloorDiv(t.w, 2)
	switch align {
	case scene.AlignStart:
		x = at.x
	case scene.AlignEnd:
		x = at.x - t.w
	}
	y := at.y - geom.FloorDiv(t.h, 2)
	switch {
	case sin >= p.c.anchor:
		y = at.y
	case sin <= -p.c.anchor:
		y = at.y - t.h
	}
	return rect{x, y, t.w, t.h}, align
}

func (p *radarPlan) legendOn() bool { return p.r.ShowLegend && len(p.r.Curves) > 0 }

func (p *radarPlan) legendOrigin() point {
	halfW, halfH := geom.FloorDiv(p.c.width, 2), geom.FloorDiv(p.c.height, 2)
	return point{geom.FloorDiv((halfW+p.c.marginRight)*3, 4), geom.FloorDiv(-(halfH+p.c.marginTop)*3, 4)}
}

func (p *radarPlan) legendRow(i int) point {
	o := p.legendOrigin()
	return point{o.x, o.y + int64(i)*p.c.legendRow}
}

func (p *radarPlan) placeLabel(i int) (rect, scene.Align, bool) {
	l, t := p.labels[i], p.texts[i]
	visible := t.w > 0
	switch l.kind {
	case radarTitle:
		return rect{-geom.FloorDiv(t.w, 2), p.frame.y - t.h, t.w, t.h}, scene.AlignMiddle, visible
	case radarAxis:
		r, align := p.axisRect(l.index, t)
		return r, align, visible
	}
	row := p.legendRow(l.index)
	return rect{row.x + p.c.marker + p.c.markerGap, row.y, t.w, t.h}, scene.AlignStart, visible && p.legendOn()
}

func (p *radarPlan) place() error {
	halfW, halfH := geom.FloorDiv(p.c.width, 2), geom.FloorDiv(p.c.height, 2)
	p.frame = rect{-(halfW + p.c.margin), -(halfH + p.c.marginTop), 2*halfW + p.c.margin + p.c.marginRight, 2*halfH + p.c.marginTop + p.c.margin}
	p.plot = rect{-p.extent, -p.extent, 2 * p.extent, 2 * p.extent}
	n := len(p.labels)
	p.rects, p.shown, p.aligns = make([]rect, n), make([]bool, n), make([]scene.Align, n)
	extent := &extent{}
	extent.addRect(p.frame)
	extent.addRect(p.plot)
	for i := range p.labels {
		p.rects[i], p.aligns[i], p.shown[i] = p.placeLabel(i)
		if p.shown[i] {
			extent.addRect(p.rects[i])
		}
	}
	p.curves = make([][]point, len(p.drawn))
	for k, index := range p.drawn {
		p.curves[k] = p.curvePoints(index)
		extent.addPoints(p.curves[k])
		if p.r.Graticule == chartmodel.GraticuleCircle {
			extent.addCurves(p.smooth(p.curves[k]))
		}
	}
	p.markers = nil
	if p.legendOn() {
		for i := range p.r.Curves {
			row := p.legendRow(i)
			p.markers = append(p.markers, rect{row.x, row.y, p.c.marker, p.c.marker})
			extent.addRect(p.markers[i])
		}
	}
	p.dx, p.dy = -extent.minX, -extent.minY
	return p.finish(extent)
}

func (p *radarPlan) shift(r rect) rect {
	r.x, r.y = r.x+p.dx, r.y+p.dy
	return r
}

func (p *radarPlan) finish(e *extent) error {
	w, err := i32(e.maxX - e.minX)
	if err != nil {
		return err
	}
	h, err := i32(e.maxY - e.minY)
	if err != nil {
		return err
	}
	p.canvas = geom.Size{W: w, H: h}
	boxes := []rect{p.plot}
	for _, points := range p.curves {
		boxes = append(boxes, boundsOf(points))
	}
	p.boxRects = make([]geom.Rect, len(boxes))
	for i, b := range boxes {
		if p.boxRects[i], err = p.shift(b).geom(); err != nil {
			return err
		}
	}
	p.labelRects = make([]geom.Rect, len(p.labels))
	for i := range p.labels {
		if !p.shown[i] {
			continue
		}
		if p.labelRects[i], err = p.shift(p.rects[i]).geom(); err != nil {
			return err
		}
	}
	p.placed = true
	return nil
}

func boundsOf(points []point) rect {
	lo, hi := points[0], points[0]
	for _, v := range points[1:] {
		lo.x, lo.y = min(lo.x, v.x), min(lo.y, v.y)
		hi.x, hi.y = max(hi.x, v.x), max(hi.y, v.y)
	}
	return rect{lo.x, lo.y, hi.x - lo.x, hi.y - lo.y}
}

type extent struct{ minX, minY, maxX, maxY int64 }

func (e *extent) addPoint(v point) {
	e.minX, e.minY = min(e.minX, v.x), min(e.minY, v.y)
	e.maxX, e.maxY = max(e.maxX, v.x), max(e.maxY, v.y)
}

func (e *extent) addRect(r rect) {
	e.addPoint(point{r.x, r.y})
	e.addPoint(point{r.x + r.w, r.y + r.h})
}

func (e *extent) addPoints(points []point) {
	for _, v := range points {
		e.addPoint(v)
	}
}

func (e *extent) addCurves(curves []bezier) {
	for _, c := range curves {
		e.addPoint(c.c1)
		e.addPoint(c.c2)
	}
}
