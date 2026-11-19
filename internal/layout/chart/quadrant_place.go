package chart

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type candidate struct {
	r     rect
	align scene.Align
}

func spread(limit int64) []int64 {
	out := []int64{0}
	for d := int64(1); d <= limit; d++ {
		out = append(out, d, -d)
	}
	return out
}

func (r rect) overlaps(o rect) bool {
	return r.w > 0 && r.h > 0 && o.w > 0 && o.h > 0 && r.x < o.x+o.w && o.x < r.x+r.w && r.y < o.y+o.h && o.y < r.y+r.h
}

func (r rect) inside(outer rect) bool {
	return r.x >= outer.x && r.y >= outer.y && r.x+r.w <= outer.x+outer.w && r.y+r.h <= outer.y+outer.h
}

func (p *quadPlan) fit(r rect) rect {
	r.x = Clamp(r.x, 0, max(p.width-r.w, 0))
	r.y = Clamp(r.y, 0, max(p.height-r.h, 0))
	return r
}

func (p *quadPlan) insidePlot(r rect) rect {
	r.x = Clamp(r.x, p.plot.x, max(p.plot.x+p.plot.w-r.w, p.plot.x))
	r.y = Clamp(r.y, p.plot.y, max(p.plot.y+p.plot.h-r.h, p.plot.y))
	return r
}

func (p *quadPlan) interior() rect {
	e := p.c.edge
	return rect{p.plot.x + e, p.plot.y + e, max(p.plot.w-2*e, 0), max(p.plot.h-2*e, 0)}
}

func (p *quadPlan) obstacles() []rect {
	if !p.cell {
		return nil
	}
	pl := p.plot
	out := []rect{{p.tiles[0].x, pl.y, 1, pl.h}, {pl.x, p.tiles[2].y, pl.w, 1}}
	return append(out, p.pointBoxes...)
}

func (p *quadPlan) free(r rect) bool {
	if !r.inside(p.interior()) {
		return false
	}
	return !slices.ContainsFunc(p.taken, r.overlaps)
}

func (p *quadPlan) search(cands []candidate) (candidate, bool) {
	if p.cell {
		for _, c := range cands {
			if p.free(c.r) {
				return c, true
			}
		}
		return cands[0], false
	}
	return cands[0], true
}

func (p *quadPlan) place() error {
	n := len(p.specs)
	p.labelRects = make([]geom.Rect, n)
	p.labelLines = make([][]string, n)
	p.aligns = make([]scene.Align, n)
	p.taken = p.obstacles()
	for _, group := range [][]quadLabelKind{{quadTitle, quadXLeft, quadXRight, quadYBottom, quadYTop}, {quadTileLabel}, {quadPointLabel}} {
		for i, s := range p.specs {
			if !slices.Contains(group, s.kind) {
				continue
			}
			if err := p.placeLabel(i); err != nil {
				return err
			}
		}
	}
	return p.placeBoxes()
}

func (p *quadPlan) placeLabel(i int) error {
	c, err := p.candidateFor(i)
	if err != nil {
		return err
	}
	g, err := c.r.geom()
	if err != nil {
		return err
	}
	p.labelRects[i], p.aligns[i] = g, c.align
	p.labelLines[i] = []string{}
	for _, line := range p.texts[i].lines {
		p.labelLines[i] = append(p.labelLines[i], line.Text)
	}
	p.taken = append(p.taken, c.r)
	return nil
}

func (p *quadPlan) candidateFor(i int) (candidate, error) {
	switch p.specs[i].kind {
	case quadTitle:
		return p.titleCandidate(i), nil
	case quadXLeft, quadXRight:
		return p.bottomCandidate(i), nil
	case quadYBottom, quadYTop:
		return p.leftCandidate(i), nil
	case quadTileLabel:
		return p.tileCandidate(i)
	}
	return p.pointCandidate(i)
}

func (p *quadPlan) titleCandidate(i int) candidate {
	t := p.texts[i]
	y := p.c.unitsY(p.o.Profile, p.c.titlePadPx)
	return candidate{p.fit(rect{geom.FloorDiv(p.width-t.w, 2), y, t.w, t.h}), scene.AlignMiddle}
}

func (p *quadPlan) bottomCandidate(i int) candidate {
	t, pl := p.texts[i], p.plot
	y := pl.y + pl.h + p.c.unitsY(p.o.Profile, p.c.xPadPx)
	_, hasLeft := p.find(quadXLeft)
	_, hasRight := p.find(quadXRight)
	if !hasLeft || !hasRight {
		return candidate{p.fit(rect{pl.x, y, t.w, t.h}), scene.AlignStart}
	}
	leftW := geom.FloorDiv(pl.w, 2)
	centre := pl.x + geom.FloorDiv(leftW, 2)
	if p.specs[i].kind == quadXRight {
		centre = pl.x + leftW + geom.FloorDiv(pl.w-leftW, 2)
	}
	return candidate{p.fit(rect{centre - geom.FloorDiv(t.w, 2), y, t.w, t.h}), scene.AlignMiddle}
}

func (p *quadPlan) leftCandidate(i int) candidate {
	t, pl := p.texts[i], p.plot
	x := pl.x - p.c.unitsX(p.o.Profile, p.c.yPadPx) - t.w
	_, hasBottom := p.find(quadYBottom)
	_, hasTop := p.find(quadYTop)
	bottom := p.specs[i].kind == quadYBottom
	var y int64
	switch {
	case hasBottom && hasTop && bottom:
		y = pl.y + pl.h - geom.FloorDiv(pl.h, 4) - geom.FloorDiv(t.h, 2)
	case hasBottom && hasTop:
		y = pl.y + geom.FloorDiv(pl.h, 4) - geom.FloorDiv(t.h, 2)
	case bottom:
		y = pl.y + pl.h - t.h
	default:
		y = pl.y
	}
	return candidate{p.fit(rect{x, y, t.w, t.h}), scene.AlignEnd}
}

func (p *quadPlan) tileCandidate(i int) (candidate, error) {
	in := p.inner[p.specs[i].index]
	t, err := p.measureAt(i, max(in.w-2*p.c.padX, 1))
	if err != nil {
		return candidate{}, err
	}
	p.texts[i] = t
	x := in.x + max(geom.FloorDiv(in.w-t.w, 2), 0)
	y := in.y + p.c.topPad
	if len(p.q.Points) == 0 {
		y = in.y + max(geom.FloorDiv(in.h-t.h, 2), 0)
	}
	var cands []candidate
	for _, dy := range spread(in.h) {
		cands = append(cands, candidate{rect{x, y + dy, t.w, t.h}, scene.AlignMiddle})
	}
	c, _ := p.search(cands)
	return c, nil
}

func (p *quadPlan) column(centre spot) rect {
	if centre.x >= p.tiles[0].x {
		return p.inner[0]
	}
	return p.inner[1]
}

func (p *quadPlan) pointCandidates(centre, r spot, t textBox) []candidate {
	right := centre.x + r.x + p.c.textPad
	top := centre.y - geom.FloorDiv(t.h, 2)
	if !p.cell {
		return []candidate{{p.insidePlot(rect{right, top, t.w, t.h}), scene.AlignStart}}
	}
	left := centre.x - (r.x + p.c.textPad - 1) - t.w
	column := p.column(centre)
	fitted := Clamp(centre.x-geom.FloorDiv(t.w, 2), column.x, max(column.x+column.w-t.w, column.x))
	offsets := spread(p.plot.h)
	var out []candidate
	for _, dy := range offsets {
		out = append(out, candidate{rect{right, top + dy, t.w, t.h}, scene.AlignStart}, candidate{rect{left, top + dy, t.w, t.h}, scene.AlignEnd})
	}
	for _, dy := range offsets {
		out = append(out, candidate{rect{fitted, top + dy, t.w, t.h}, scene.AlignMiddle})
	}
	return out
}

func (p *quadPlan) pointWrap(centre spot) int64 {
	return max(p.column(centre).w, 2)
}

func (p *quadPlan) pointCandidate(i int) (candidate, error) {
	centre, r := p.centres[p.specs[i].index], p.radii[p.specs[i].index]
	var best candidate
	for _, target := range []int64{0, p.pointWrap(centre)} {
		t, err := p.measureAt(i, target)
		if err != nil {
			return candidate{}, err
		}
		p.texts[i] = t
		c, found := p.search(p.pointCandidates(centre, r, t))
		best = c
		if found {
			break
		}
	}
	return best, nil
}

func (p *quadPlan) boxRect(b quadBox) rect {
	switch b.kind {
	case quadPlot:
		return p.plot
	case quadTile:
		return p.tiles[b.index]
	}
	return p.pointBoxes[b.index]
}

func (p *quadPlan) placeBoxes() error {
	p.boxRects = make([]geom.Rect, len(p.boxes))
	for i, b := range p.boxes {
		g, err := p.boxRect(b).geom()
		if err != nil {
			return err
		}
		p.boxRects[i] = g
	}
	p.laidOut = true
	return nil
}
