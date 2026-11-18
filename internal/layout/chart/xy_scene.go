package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const seriesCount = 12

type segment struct{ x0, y0, x1, y1 int64 }

func pointOf(x, y int64) (geom.Point, error) {
	px, err := i32(x)
	if err != nil {
		return geom.Point{}, err
	}
	py, err := i32(y)
	if err != nil {
		return geom.Point{}, err
	}
	return geom.Point{X: px, Y: py}, nil
}

func barShape(plot int) scene.Shape {
	return scene.Shape{Style: "series", Series: uint8(plot % seriesCount)}
}

func lineShape(plot int) scene.Shape {
	lines := [...]scene.LineStyle{scene.LineSolid, scene.LineDashed, scene.LineDotted}
	return scene.Shape{Style: "series-line", Series: uint8(plot % seriesCount), Width: scene.Width{Kind: scene.WidthEmphasis}, Line: lines[plot%len(lines)]}
}

func (p *xyPlan) axisSegments(a *axis) []segment {
	sp, edge := a.space, p.c.edge
	var out []segment
	switch a.position {
	case posBottom:
		y := a.area.y + geom.FloorDiv(sp.line, 2)
		out = append(out, segment{a.r0, y, a.r1 - edge, y})
		for k := range a.count() {
			x := a.tickPosition(k, edge)
			out = append(out, segment{x, y, x, a.area.y + sp.line + sp.tick - edge})
		}
	case posLeft:
		x := a.area.x + a.area.w - sp.line + geom.FloorDiv(sp.line, 2)
		out = append(out, segment{x, a.r0, x, a.r1 - edge})
		for k := range a.count() {
			y := a.tickPosition(k, edge)
			out = append(out, segment{x, y, a.area.x + a.area.w - sp.line - sp.tick, y})
		}
	default:
		y := a.area.y + a.area.h - sp.line + geom.FloorDiv(sp.line, 2)
		out = append(out, segment{a.r0, y, a.r1 - edge, y})
		for k := range a.count() {
			x := a.tickPosition(k, edge)
			out = append(out, segment{x, y, x, a.area.y + a.area.h - sp.line - sp.tick})
		}
	}
	return out
}

func (p *xyPlan) axisPrimitives(a *axis) ([]scene.Primitive, error) {
	var out []scene.Primitive
	for i, s := range p.axisSegments(a) {
		isLine := i == 0
		if (isLine && a.space.line == 0) || (!isLine && a.space.tick == 0) || (s.x0 == s.x1 && s.y0 == s.y1) {
			continue
		}
		from, err := pointOf(s.x0, s.y0)
		if err != nil {
			return nil, err
		}
		to, err := pointOf(s.x1, s.y1)
		if err != nil {
			return nil, err
		}
		out = append(out, &scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{from, to}})
	}
	return out, nil
}

func (p *xyPlan) groups() ([]*scene.Group, error) {
	var groups []*scene.Group
	var axes []scene.Primitive
	for _, a := range []*axis{&p.x, &p.y} {
		items, err := p.axisPrimitives(a)
		if err != nil {
			return nil, err
		}
		axes = append(axes, items...)
	}
	if len(axes) > 0 {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleDecor, Items: axes})
	}
	for i, b := range p.boxes {
		items, err := p.boxItems(i, b)
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: b.id, Items: items})
	}
	return groups, nil
}

func (p *xyPlan) boxItems(i int, b boxSpec) ([]scene.Primitive, error) {
	var items []scene.Primitive
	var err error
	switch {
	case b.isPlot:
		items, err = p.legendMarkers()
	case b.isLine:
		var path *scene.Path
		path, err = p.linePath(b.plot)
		items = []scene.Primitive{path}
	default:
		items = []scene.Primitive{&scene.Rect{Shape: barShape(b.plot), Rect: p.boxRects[i]}}
	}
	if err != nil {
		return nil, err
	}
	return append(items, p.textItems(b.id)...), nil
}

func (p *xyPlan) lineRuns(plot chartmodel.Plot) [][]chartmodel.Point {
	var runs [][]chartmodel.Point
	open := false
	for _, point := range plot.Points {
		switch {
		case !point.Present:
			open = false
		case open:
			runs[len(runs)-1] = append(runs[len(runs)-1], point)
		default:
			runs, open = append(runs, []chartmodel.Point{point}), true
		}
	}
	return runs
}

func (p *xyPlan) linePath(index int) (*scene.Path, error) {
	path := &scene.Path{Shape: lineShape(index)}
	for _, run := range p.lineRuns(p.xy.Plots[index]) {
		for j, point := range run {
			x, y := p.pointXY(point)
			at, err := pointOf(x, y)
			if err != nil {
				return nil, err
			}
			if j == 0 {
				path.Commands = append(path.Commands, &scene.MoveTo{P: at})
			}
			if j > 0 || len(run) == 1 {
				path.Commands = append(path.Commands, &scene.LineTo{P: at})
			}
		}
	}
	return path, nil
}

func (p *xyPlan) legendMarkers() ([]scene.Primitive, error) {
	if !p.legendOn {
		return nil, nil
	}
	c := p.c
	var items []scene.Primitive
	for i, plot := range p.xy.Plots {
		row := p.legend.y + c.legendPad + int64(i)*(p.legendLH+c.itemGap)
		x, y := p.legend.x+c.legendPad, row+geom.FloorDiv(p.legendLH-c.legendMarker, 2)
		if plot.Kind == chartmodel.PlotBar {
			g, err := rect{x, y, c.legendMarker, c.legendMarker}.geom()
			if err != nil {
				return nil, err
			}
			items = append(items, &scene.Rect{Shape: barShape(i), Rect: g})
			continue
		}
		from, err := pointOf(x, y+geom.FloorDiv(c.legendMarker, 2))
		if err != nil {
			return nil, err
		}
		to, err := pointOf(x+c.legendMarker-c.edge, y+geom.FloorDiv(c.legendMarker, 2))
		if err != nil {
			return nil, err
		}
		items = append(items, &scene.Path{Shape: lineShape(i), Commands: []scene.Command{&scene.MoveTo{P: from}, &scene.LineTo{P: to}}})
	}
	return items, nil
}

func (p *xyPlan) textItems(owner string) []scene.Primitive {
	var items []scene.Primitive
	for i, s := range p.specs {
		if s.owner == owner && p.shown[i] {
			items = append(items, p.textItem(i))
		}
	}
	return items
}

func textRole(role measure.Role) scene.TextRole {
	switch role {
	case measure.RoleTitle:
		return scene.TextRoleTitle
	case measure.RoleBody:
		return scene.TextRoleBody
	}
	return scene.TextRoleLabel
}

func (p *xyPlan) textItem(i int) *scene.Text {
	s := p.specs[i]
	role, size := p.styleOf(s)
	style := "text"
	if s.kind == labelXTick || s.kind == labelYTick {
		style = "text-muted"
	}
	lines := make([][]scene.Run, len(p.texts[i].lines))
	for j, line := range p.texts[i].lines {
		for _, run := range line.Runs {
			lines[j] = append(lines[j], scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
		}
	}
	return &scene.Text{Rect: p.labelRects[i], Role: textRole(role), Size: size, Align: p.aligns[i], Style: style, Lines: lines}
}
