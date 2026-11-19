package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
)

func (p *quadPlan) measureKinds(target int64, kinds ...quadLabelKind) (widest, tallest int64, found bool, err error) {
	for _, kind := range kinds {
		i, ok := p.find(kind)
		if !ok {
			continue
		}
		t, err := p.measureAt(i, target)
		if err != nil {
			return 0, 0, false, err
		}
		p.texts[i] = t
		widest, tallest, found = max(widest, t.w), max(tallest, t.h), true
	}
	return widest, tallest, found, nil
}

func (p *quadPlan) arrangeTitle() (int64, error) {
	_, tallest, found, err := p.measureKinds(p.c.width-2*p.c.padX, quadTitle)
	if err != nil || !found {
		return 0, err
	}
	lh := p.lineHeight(measure.RoleTitle, int32(p.c.titleFontPx))
	return max(p.c.titleBand+tallest-lh, p.c.unitsY(p.o.Profile, p.c.titlePadPx)+tallest), nil
}

func (p *quadPlan) arrangeLeft() (int64, error) {
	pad := p.c.unitsX(p.o.Profile, p.c.yPadPx)
	target := max(geom.FloorDiv(p.c.width, 2)-2*pad-2*p.c.padX, 1)
	widest, _, found, err := p.measureKinds(target, quadYBottom, quadYTop)
	if err != nil || !found {
		return 0, err
	}
	return max(p.c.yBand, widest+2*pad), nil
}

func (p *quadPlan) arrangeBottom(plotW int64) (int64, error) {
	_, hasLeft := p.find(quadXLeft)
	_, hasRight := p.find(quadXRight)
	target := plotW
	if hasLeft && hasRight {
		target = geom.FloorDiv(plotW, 2)
	}
	_, tallest, found, err := p.measureKinds(max(target, 1), quadXLeft, quadXRight)
	if err != nil || !found {
		return 0, err
	}
	lh := p.lineHeight(measure.RoleLabel, int32(p.c.xFontPx))
	return max(p.c.xBand+tallest-lh, p.c.unitsY(p.o.Profile, p.c.xPadPx)+tallest), nil
}

func (p *quadPlan) arrange() error {
	c := &p.c
	p.texts = make([]textBox, len(p.specs))
	titleBand, err := p.arrangeTitle()
	if err != nil {
		return err
	}
	leftBand, err := p.arrangeLeft()
	if err != nil {
		return err
	}
	plotW := max(c.width-2*c.padX-leftBand, minPlot)
	bottomBand, err := p.arrangeBottom(plotW)
	if err != nil {
		return err
	}
	plotH := max(c.height-2*c.padY-titleBand-bottomBand, minPlot)
	p.width = 2*c.padX + leftBand + plotW
	p.height = 2*c.padY + titleBand + plotH + bottomBand
	p.plot = rect{c.padX + leftBand, c.padY + titleBand, plotW, plotH}
	p.arrangeTiles()
	p.arrangePoints()
	return nil
}

func (p *quadPlan) arrangeTiles() {
	pl, e := p.plot, p.c.edge
	leftW, topH := geom.FloorDiv(pl.w, 2), geom.FloorDiv(pl.h, 2)
	cols := [2][2]int64{{pl.x, pl.x + leftW}, {pl.x + leftW, pl.x + pl.w}}
	rows := [2][2]int64{{pl.y, pl.y + topH}, {pl.y + topH, pl.y + pl.h}}
	for i, at := range [tileCount][2]int{{1, 0}, {0, 0}, {0, 1}, {1, 1}} {
		col, row := cols[at[0]], rows[at[1]]
		p.tiles[i] = rect{col[0], row[0], col[1] - col[0], row[1] - row[0]}
		right, bottom := col[1], row[1]
		if at[0] == 1 {
			right -= e
		}
		if at[1] == 1 {
			bottom -= e
		}
		p.inner[i] = rect{col[0] + e, row[0] + e, max(right-col[0]-e, 0), max(bottom-row[0]-e, 0)}
	}
}

func (p *quadPlan) radiusOf(pt QuadrantPoint) spot {
	if pt.Radius == NoPointRadius {
		return spot{p.c.radiusX, p.c.radiusY}
	}
	return spot{p.c.unitsX(p.o.Profile, pt.Radius), p.c.unitsY(p.o.Profile, pt.Radius)}
}

func (p *quadPlan) arrangePoints() {
	pl, e := p.plot, p.c.edge
	spanW, spanH := max(pl.w-3*e, 0), max(pl.h-3*e, 0)
	for _, pt := range p.q.Points {
		centre := spot{pl.x + e + geom.FloorDiv(pt.X*spanW, scale), pl.y + e + spanH - geom.FloorDiv(pt.Y*spanH, scale)}
		r := p.radiusOf(pt)
		p.centres = append(p.centres, centre)
		p.radii = append(p.radii, r)
		p.pointBoxes = append(p.pointBoxes, p.markerBox(centre, r))
	}
}

func (p *quadPlan) markerBox(c, r spot) rect {
	switch {
	case !p.cell:
		return rect{c.x - r.x, c.y - r.y, 2 * r.x, 2 * r.y}.within(p.plot)
	case r.x <= 1 && r.y <= 1:
		return rect{c.x, c.y, 1, 1}
	}
	return rect{c.x - r.x, c.y - r.y, 2*r.x + 1, 2*r.y + 1}.within(p.plot)
}
