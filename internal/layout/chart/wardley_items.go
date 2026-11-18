package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type itemBuilder struct {
	items []scene.Primitive
	err   error
}

func (b *itemBuilder) point(x, y int64) geom.Point {
	g, err := pointOf(x, y)
	if err != nil && b.err == nil {
		b.err = err
	}
	return g
}

func (b *itemBuilder) side(v int64) int32 {
	out, err := i32(v)
	if err != nil && b.err == nil {
		b.err = err
	}
	return out
}

func (b *itemBuilder) points(pts []pt) []geom.Point {
	out := make([]geom.Point, len(pts))
	for i, q := range pts {
		out[i] = b.point(q.x, q.y)
	}
	return out
}

func (b *itemBuilder) circle(shape scene.Shape, at pt, r int64) {
	b.items = append(b.items, &scene.Ellipse{Shape: shape, CX: b.side(at.x), CY: b.side(at.y), RX: b.side(r), RY: b.side(r)})
}

func (b *itemBuilder) rect(shape scene.Shape, r rect) {
	g, err := r.geom()
	if err != nil && b.err == nil {
		b.err = err
	}
	b.items = append(b.items, &scene.Rect{Shape: shape, Rect: g})
}

func (b *itemBuilder) polygon(shape scene.Shape, pts []pt) {
	b.items = append(b.items, &scene.Polygon{Shape: shape, Points: b.points(pts)})
}

func (b *itemBuilder) polyline(shape scene.Shape, pts []pt) {
	b.items = append(b.items, &scene.Polyline{Shape: shape, Points: b.points(pts)})
}

func (b *itemBuilder) openPath(shape scene.Shape, pts []pt) { b.addPath(shape, pts, nil) }

func (b *itemBuilder) closedPath(shape scene.Shape, pts []pt) {
	b.addPath(shape, pts, []scene.Command{&scene.ClosePath{}})
}

func (b *itemBuilder) addPath(shape scene.Shape, pts []pt, tail []scene.Command) {
	cmds := make([]scene.Command, 0, len(pts)+len(tail))
	for i, q := range pts {
		if i == 0 {
			cmds = append(cmds, &scene.MoveTo{P: b.point(q.x, q.y)})
			continue
		}
		cmds = append(cmds, &scene.LineTo{P: b.point(q.x, q.y)})
	}
	b.items = append(b.items, &scene.Path{Shape: shape, Commands: append(cmds, tail...)})
}

func (b *itemBuilder) symbol(name, style string, at pt) {
	b.items = append(b.items, &scene.SymbolRef{Symbol: name, At: b.point(at.x, at.y), Style: style})
}

func (b *itemBuilder) marker(at pt, axis scene.Axis) {
	b.items = append(b.items, &scene.MarkerRef{Marker: markerPoint, At: b.point(at.x, at.y), Axis: axis})
}

func styled(name string) scene.Shape { return scene.Shape{Style: name} }

func lined(name string, line scene.LineStyle) scene.Shape {
	return scene.Shape{Style: name, Line: line}
}

func (p *wardleyPlan) nodeItems(k int) ([]scene.Primitive, error) {
	n, at := p.w.Nodes[k], p.pos[k]
	if n.Anchor {
		return nil, nil
	}
	b := &itemBuilder{}
	if p.cell {
		p.cellNode(b, n, at)
	} else {
		p.vectorNode(b, n, at)
	}
	return b.items, b.err
}

func cellSymbol(n WardleyNode) (name, style string) {
	if n.PipelineParent {
		return "box-hollow", "mark-hollow"
	}
	switch n.Strategy {
	case WardleyBuild:
		return "diamond-hollow", "mark-hollow"
	case WardleyBuy:
		return "diamond", "mark"
	case WardleyOutsource:
		return "disc", "mark"
	case WardleyMarket:
		return "bullseye", "mark"
	}
	return "ring", "mark-hollow"
}

func (p *wardleyPlan) cellNode(b *itemBuilder, n WardleyNode, at pt) {
	name, style := cellSymbol(n)
	b.symbol(name, style, at)
	if n.Inertia {
		b.rect(styled("ink"), rect{at.x + p.c.inertiaGap, at.y, 1, 1})
	}
}

func (p *wardleyPlan) vectorNode(b *itemBuilder, n WardleyNode, at pt) {
	c := p.c
	if n.PipelineParent {
		half := geom.FloorDiv(c.squareSize, 2)
		b.rect(styled("node"), rect{at.x - half, at.y - half, c.squareSize, c.squareSize})
	} else {
		p.strategyShapes(b, n, at)
		b.circle(styled("mark-hollow"), at, c.nodeRadius)
	}
	if n.Inertia {
		reach := p.reach(n)
		x := at.x + reach + c.inertiaGap
		bar := scene.Shape{Style: "ink-line", Width: scene.Width{Kind: scene.WidthUnits, Units: b.side(c.inertiaWidth)}}
		b.polyline(bar, []pt{{x, at.y - reach}, {x, at.y + reach}})
	}
}

func (p *wardleyPlan) strategyShapes(b *itemBuilder, n WardleyNode, at pt) {
	outer := 2 * p.c.nodeRadius
	switch n.Strategy {
	case WardleyBuild:
		b.circle(lined("mark-hollow", scene.LineDashed), at, outer)
	case WardleyBuy:
		b.circle(styled("mark"), at, outer)
	case WardleyOutsource:
		b.circle(styled("ink"), at, outer)
	case WardleyMarket:
		p.marketShapes(b, at, outer)
	}
}

func (p *wardleyPlan) marketShapes(b *itemBuilder, at pt, outer int64) {
	c := p.c
	b.circle(styled("mark-hollow"), at, outer)
	side := geom.FloorDiv(7*c.marketRing, 8)
	corners := []pt{{at.x, at.y - c.marketRing}, {at.x - side, at.y + geom.FloorDiv(c.marketRing, 2)}, {at.x + side, at.y + geom.FloorDiv(c.marketRing, 2)}}
	b.polygon(styled("rule"), corners)
	for _, q := range corners {
		b.circle(styled("mark-hollow"), q, c.marketDot)
	}
}

func (p *wardleyPlan) ghostItems(k int) ([]scene.Primitive, error) {
	b := &itemBuilder{}
	if p.cell {
		b.symbol("ring", "mark-hollow", p.ghosts[k])
	} else {
		b.circle(lined("mark-hollow", scene.LineDotted), p.ghosts[k], p.c.nodeRadius)
	}
	return b.items, b.err
}

func (p *wardleyPlan) acceleratorItems(r rect) ([]scene.Primitive, error) {
	return p.arrowItems(p.forcePoints(r))
}

func (p *wardleyPlan) deacceleratorItems(r rect) ([]scene.Primitive, error) {
	pts := p.forcePoints(r)
	left, right := r.x, r.x+r.w-p.c.edge
	for i := range pts {
		pts[i].x = left + right - pts[i].x
	}
	return p.arrowItems(pts)
}

func (p *wardleyPlan) forcePoints(r rect) []pt {
	c := p.c
	half := c.arrowShaft + c.arrowHead
	cy, x0, x1 := r.y+half, r.x, r.x+r.w-c.edge
	tip := x1 - c.arrowTip
	return []pt{{x0, cy - c.arrowShaft}, {tip, cy - c.arrowShaft}, {tip, cy - half}, {x1, cy}, {tip, cy + half}, {tip, cy + c.arrowShaft}, {x0, cy + c.arrowShaft}}
}

func (p *wardleyPlan) arrowItems(pts []pt) ([]scene.Primitive, error) {
	b := &itemBuilder{}
	b.polygon(styled("mark-hollow"), pts)
	return b.items, b.err
}

func (p *wardleyPlan) annotationItems(k int) ([]scene.Primitive, error) {
	b := &itemBuilder{}
	if !p.cell {
		b.circle(styled("mark-hollow"), p.points[k], p.c.annotationRadius)
	}
	return b.items, b.err
}

func (p *wardleyPlan) boxItems() ([]scene.Primitive, error) {
	b := &itemBuilder{}
	b.rect(styled("note"), p.box)
	return b.items, b.err
}

func (p *wardleyPlan) frameItems(k int) ([]scene.Primitive, error) {
	r := p.frames[k]
	x1, y1 := r.x+r.w-p.c.edge, r.y+r.h-p.c.edge
	b := &itemBuilder{}
	b.closedPath(styled("group"), []pt{{r.x, r.y}, {x1, r.y}, {x1, y1}, {r.x, y1}})
	return b.items, b.err
}

func (p *wardleyPlan) decorItems() ([]scene.Primitive, error) {
	pl := p.plot
	right, bottom := pl.x+pl.w, pl.y+pl.h
	b := &itemBuilder{}
	b.openPath(styled("rule"), []pt{{pl.x, pl.y}, {pl.x, bottom}, {right, bottom}})
	for i := 0; i+1 < len(p.w.Stages); i++ {
		_, x := p.stageSpan(i)
		b.openPath(lined("rule", scene.LineDotted), []pt{{x, pl.y}, {x, bottom}})
	}
	return b.items, b.err
}
