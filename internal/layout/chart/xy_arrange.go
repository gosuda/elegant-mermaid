package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
)

func (p *xyPlan) hasBars() bool {
	for _, plot := range p.xy.Plots {
		if plot.Kind == chartmodel.PlotBar {
			return true
		}
	}
	return false
}

func (p *xyPlan) titleBlock(index int, pad int64) int64 {
	return p.texts[index].h + 2*pad
}

func (p *xyPlan) titleSpace(availH int64) int64 {
	i, ok := p.find(labelTitle)
	if !ok {
		return 0
	}
	need := p.titleBlock(i, p.c.titlePad)
	p.titleShown = need <= availH
	if !p.titleShown {
		return 0
	}
	return need
}

func (p *xyPlan) sideTitleSpace(availH int64) int64 {
	kind := labelYTitle
	if p.horizontal() {
		kind = labelXTitle
	}
	i, ok := p.find(kind)
	if !ok {
		return 0
	}
	need := p.titleBlock(i, p.c.axisTitlePad)
	p.sideTitle, p.sideShown = i, need <= availH
	if !p.sideShown {
		return 0
	}
	return need
}

func (p *xyPlan) tickKind(a *axis) labelKind {
	if a == &p.x {
		return labelXTick
	}
	return labelYTick
}

func (p *xyPlan) titleKind(a *axis) labelKind {
	if a == &p.y {
		return labelYTitle
	}
	return labelXTitle
}

func (p *xyPlan) horizontalSpace(a *axis, availW, availH int64) bandSpace {
	c := p.c
	space := bandSpace{w: availW}
	h := availH
	if h > c.axisLine {
		h -= c.axisLine
		space.line = c.axisLine
	}
	if a.showLabels {
		a.labelW, a.labelH = p.tickExtent(p.tickKind(a))
		a.outer = min(geom.FloorDiv(a.labelW, 2), geom.FloorDiv(c.outerMax*availW, 1000))
		if need := a.labelH + 2*c.padY; need <= h {
			h -= need
			space.showLabel = true
		}
	}
	if h >= c.tickLen {
		h -= c.tickLen
		space.tick = c.tickLen
	}
	if i, ok := p.find(p.titleKind(a)); ok {
		if need := p.titleBlock(i, c.axisTitlePad); need <= h {
			h -= need
			space.title = need
		}
	}
	space.h = availH - h
	return space
}

func (p *xyPlan) verticalSpace(a *axis, availW, availH int64) bandSpace {
	c := p.c
	space := bandSpace{h: availH}
	w := availW
	if w > c.axisLine {
		w -= c.axisLine
		space.line = c.axisLine
	}
	if a.showLabels {
		a.labelW, a.labelH = p.tickExtent(p.tickKind(a))
		a.outer = min(geom.FloorDiv(a.labelH, 2), geom.FloorDiv(c.outerMax*availH, 1000))
		if need := a.labelW + 2*c.padX; need <= w {
			w -= need
			space.showLabel = true
		}
	}
	if w >= c.tickLen {
		w -= c.tickLen
		space.tick = c.tickLen
	}
	space.w = availW - w
	return space
}

func (p *xyPlan) legendSize(availW, availH int64) (w, h int64, beside bool) {
	var widest int64
	for i, s := range p.specs {
		if s.kind != labelLegend {
			continue
		}
		widest = max(widest, p.texts[i].w)
		p.legendLH = max(p.legendLH, p.texts[i].h)
		p.legendRows++
	}
	if p.legendRows == 0 {
		return 0, 0, false
	}
	c := p.c
	w = 2*c.legendPad + c.legendMarker + c.markerGap + widest
	h = 2*c.legendPad + p.legendRows*p.legendLH + (p.legendRows-1)*c.itemGap
	return w, h, w <= availW && h <= availH
}

func (p *xyPlan) legendBeside(w, h int64) rect {
	pl := p.plot
	return rect{pl.x + pl.w, pl.y + max(geom.FloorDiv(pl.h-h, 2), 0), w, h}
}

func (p *xyPlan) legendOverlay(w, h int64) rect {
	pl := p.plot
	return p.fit(rect{pl.x + pl.w - w, pl.y, w, h})
}

func (p *xyPlan) arrange() {
	c := p.c
	p.width, p.height = c.width, c.height
	chartW := geom.FloorDiv(p.width*c.reserved, 100)
	chartH := geom.FloorDiv(p.height*c.reserved, 100)
	availW, availH := p.width-chartW, p.height-chartH
	titleH := p.titleSpace(availH)
	p.titleH = titleH
	availH -= titleH
	sideH := p.sideTitleSpace(availH)
	availH -= sideH
	top := titleH + sideH
	var plotX, plotY int64
	if p.horizontal() {
		p.x.space = p.verticalSpace(&p.x, availW, availH)
		availW -= p.x.space.w
		plotX = p.x.space.w
		p.y.space = p.horizontalSpace(&p.y, availW, availH)
		availH -= p.y.space.h
		plotY = top + p.y.space.h
	} else {
		p.x.space = p.horizontalSpace(&p.x, availW, availH)
		availH -= p.x.space.h
		p.y.space = p.verticalSpace(&p.y, availW, availH)
		plotX, plotY = p.y.space.w, top
		availW -= p.y.space.w
	}
	legendW, legendH, beside := p.legendSize(availW, chartH)
	p.legendOn = p.legendRows > 0
	if beside {
		availW -= legendW
	}
	chartW = max(chartW+max(availW, 0), c.edge)
	chartH = max(chartH+max(availH, 0), c.edge)
	p.plot = rect{max(min(plotX, p.width-chartW), 0), max(min(plotY, p.height-chartH), 0), chartW, chartH}
	if beside {
		p.legend = p.legendBeside(legendW, legendH)
	} else {
		p.legend = p.legendOverlay(legendW, legendH)
	}
	p.setAreas(top)
}

func (p *xyPlan) setAreas(top int64) {
	pl := p.plot
	if p.horizontal() {
		p.x.area = rect{0, pl.y, p.x.space.w, pl.h}
		p.y.area = rect{pl.x, top, pl.w, p.y.space.h}
		p.x.r0, p.x.r1 = pl.y, pl.y+pl.h
		p.y.r0, p.y.r1 = pl.x, pl.x+pl.w
	} else {
		p.x.area = rect{pl.x, pl.y + pl.h, pl.w, p.x.space.h}
		p.y.area = rect{0, pl.y, p.y.space.w, pl.h}
		p.x.r0, p.x.r1 = pl.x, pl.x+pl.w
		p.y.r0, p.y.r1 = pl.y, pl.y+pl.h
	}
	if p.hasBars() {
		p.x.raiseOuterForBars(p.c.barRatio)
	}
}
