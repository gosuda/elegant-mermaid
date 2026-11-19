package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *radarPlan) at(v point) (geom.Point, error) { return pointOf(v.x+p.dx, v.y+p.dy) }

func (p *radarPlan) atAll(points []point) ([]geom.Point, error) {
	out := make([]geom.Point, len(points))
	for i, v := range points {
		g, err := p.at(v)
		if err != nil {
			return nil, err
		}
		out[i] = g
	}
	return out, nil
}

func ruleShape() scene.Shape { return scene.Shape{Style: "rule"} }

func tintShape(curve int) scene.Shape {
	return scene.Shape{Style: "series-tint", Series: uint8(curve % radarSeries)}
}

func (p *radarPlan) ring(radius int64) (scene.Primitive, error) {
	if p.r.Graticule == chartmodel.GraticuleCircle {
		centre, err := p.at(point{})
		if err != nil {
			return nil, err
		}
		r, err := i32(radius)
		if err != nil {
			return nil, err
		}
		return &scene.Ellipse{Shape: ruleShape(), CX: centre.X, CY: centre.Y, RX: r, RY: r}, nil
	}
	points, err := p.atAll(p.vertices(radius))
	if err != nil {
		return nil, err
	}
	if len(points) >= 3 {
		return &scene.Polygon{Shape: ruleShape(), Points: points}, nil
	}
	if len(points) == 2 {
		return &scene.Polyline{Shape: ruleShape(), Points: points}, nil
	}
	return nil, nil
}

func (p *radarPlan) underlay() ([]scene.Primitive, error) {
	var items []scene.Primitive
	for _, radius := range p.rings {
		if radius == 0 {
			continue
		}
		item, err := p.ring(radius)
		if err != nil {
			return nil, err
		}
		if item != nil {
			items = append(items, item)
		}
	}
	if p.radius == 0 {
		return items, nil
	}
	centre, err := p.at(point{})
	if err != nil {
		return nil, err
	}
	tips, err := p.atAll(p.vertices(p.radius))
	if err != nil {
		return nil, err
	}
	for _, tip := range tips {
		items = append(items, &scene.Polyline{Shape: ruleShape(), Points: []geom.Point{centre, tip}})
	}
	return items, nil
}

func (p *radarPlan) curvePath(k int) (*scene.Path, error) {
	index := p.drawn[k]
	points := p.curves[k]
	first, err := p.at(points[0])
	if err != nil {
		return nil, err
	}
	path := &scene.Path{Shape: tintShape(index), Commands: []scene.Command{&scene.MoveTo{P: first}}}
	if p.r.Graticule == chartmodel.GraticuleCircle {
		err = p.smoothCommands(path, points)
	} else {
		err = p.lineCommands(path, points[1:])
	}
	if err != nil {
		return nil, err
	}
	path.Commands = append(path.Commands, &scene.ClosePath{})
	return path, nil
}

func (p *radarPlan) lineCommands(path *scene.Path, points []point) error {
	for _, v := range points {
		g, err := p.at(v)
		if err != nil {
			return err
		}
		path.Commands = append(path.Commands, &scene.LineTo{P: g})
	}
	return nil
}

func (p *radarPlan) smoothCommands(path *scene.Path, points []point) error {
	for _, b := range p.smooth(points) {
		g, err := p.atAll([]point{b.c1, b.c2, b.to})
		if err != nil {
			return err
		}
		path.Commands = append(path.Commands, &scene.CubicTo{C1: g[0], C2: g[1], P: g[2]})
	}
	return nil
}

func (p *radarPlan) textItem(i int) *scene.Text {
	role, size := radarRole(p.labels[i])
	lines := make([][]scene.Run, len(p.texts[i].lines))
	for j, line := range p.texts[i].lines {
		for _, run := range line.Runs {
			lines[j] = append(lines[j], scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
		}
	}
	return &scene.Text{Rect: p.labelRects[i], Role: textRole(role), Size: size, Align: p.aligns[i], Style: "text", Lines: lines}
}

func (p *radarPlan) textItems(kind radarLabelKind) []scene.Primitive {
	var items []scene.Primitive
	for i, l := range p.labels {
		if l.kind == kind && p.shown[i] {
			items = append(items, p.textItem(i))
		}
	}
	return items
}

func (p *radarPlan) overlay() ([]scene.Primitive, error) {
	items := p.textItems(radarTitle)
	for i, marker := range p.markers {
		g, err := p.shift(marker).geom()
		if err != nil {
			return nil, err
		}
		items = append(items, &scene.Rect{Shape: scene.Shape{Style: "series", Series: uint8(i % radarSeries)}, Rect: g})
	}
	return append(items, p.textItems(radarLegend)...), nil
}

func (p *radarPlan) groups() ([]*scene.Group, error) {
	under, err := p.underlay()
	if err != nil {
		return nil, err
	}
	groups := []*scene.Group{}
	if len(under) > 0 {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleDecor, Items: under})
	}
	groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: radarPlotID, Items: p.textItems(radarAxis)})
	for k, index := range p.drawn {
		path, err := p.curvePath(k)
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: radarCurveID(index), Items: []scene.Primitive{path}})
	}
	over, err := p.overlay()
	if err != nil {
		return nil, err
	}
	if len(over) > 0 {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleDecor, Items: over})
	}
	return groups, nil
}
