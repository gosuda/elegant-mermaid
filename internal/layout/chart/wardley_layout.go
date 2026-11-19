package chart

import (
	"context"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const wardleyDiagram = "wardley"

func LayoutWardley(ctx context.Context, w *Wardley, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	if err := ctx.Err(); err != nil {
		return scene.Scene{}, nil, err
	}
	p, err := newWardleyPlan(w, o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.measureAll(); err != nil {
		return scene.Scene{}, nil, err
	}
	p.arrange()
	if err = p.finish(); err != nil {
		return scene.Scene{}, nil, err
	}
	return p.scene()
}

func (p *wardleyPlan) finish() error {
	if err := p.placeLabels(); err != nil {
		return err
	}
	p.grow()
	if err := p.placeBoxes(); err != nil {
		return err
	}
	return p.buildRoutes()
}

func (p *wardleyPlan) scene() (scene.Scene, []diag.Diagnostic, error) {
	width, err := i32(p.width)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	height, err := i32(p.height)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	options := p.o
	options.Direction = scene.DirectionTB
	dump := scene.Dump{Stage: scene.StageLayout, Kind: wardleyDiagram, Options: options, Canvas: geom.Size{W: width, H: height}, Boxes: p.dumpBoxes(), Routes: p.routes, Labels: p.dumpLabels()}
	groups, err := p.groups()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: groups}, nil, nil
}

func (p *wardleyPlan) routeItems(i int) ([]scene.Primitive, error) {
	r := p.routes[i]
	a, b := pt{int64(r.Points[0].X), int64(r.Points[0].Y)}, pt{int64(r.Points[1].X), int64(r.Points[1].Y)}
	items := &itemBuilder{}
	items.openPath(scene.Shape{Style: "edge", Line: strokeLine(r.Stroke)}, []pt{a, b})
	if r.MarkerStart == markerPoint {
		at, axis := p.arrowhead(b, a, p.reachOf(r.From))
		items.marker(at, axis)
	}
	if r.MarkerEnd == markerPoint {
		at, axis := p.arrowhead(a, b, p.reachOf(r.To))
		items.marker(at, axis)
	}
	return append(items.items, p.textItems(r.ID)...), items.err
}

func strokeLine(stroke string) scene.LineStyle {
	switch stroke {
	case strokeDashed:
		return scene.LineDashed
	case strokeDotted:
		return scene.LineDotted
	}
	return scene.LineSolid
}

func (p *wardleyPlan) reachOf(id string) int64 {
	if k, ok := nodeIndex(id); ok && k < len(p.w.Nodes) {
		return p.reach(p.w.Nodes[k])
	}
	return p.c.nodeRadius
}

func wardleyMarkerAxis(dx, dy int64) scene.Axis {
	horizontal := max(dx, -dx) >= max(dy, -dy)
	switch {
	case horizontal && dx >= 0:
		return scene.AxisPlusX
	case horizontal:
		return scene.AxisMinusX
	case dy >= 0:
		return scene.AxisPlusY
	}
	return scene.AxisMinusY
}

func (p *wardleyPlan) arrowhead(from, to pt, reach int64) (pt, scene.Axis) {
	dx, dy := to.x-from.x, to.y-from.y
	axis := wardleyMarkerAxis(dx, dy)
	if dx == 0 && dy == 0 {
		return to, axis
	}
	if p.cell {
		return stepBack(to, axis), axis
	}
	length, err := geom.Isqrt(dx*dx + dy*dy)
	if err != nil {
		return to, axis
	}
	return pt{to.x - measure.RoundHalfUp(dx*reach, length), to.y - measure.RoundHalfUp(dy*reach, length)}, axis
}

func stepBack(to pt, axis scene.Axis) pt {
	switch axis {
	case scene.AxisPlusX:
		return pt{to.x - 1, to.y}
	case scene.AxisMinusX:
		return pt{to.x + 1, to.y}
	case scene.AxisPlusY:
		return pt{to.x, to.y - 1}
	}
	return pt{to.x, to.y + 1}
}
