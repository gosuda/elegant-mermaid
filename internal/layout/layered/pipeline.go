package layered

import (
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type Input struct {
	Kind    string
	Boxes   []scene.Box
	Routes  []scene.Route
	Text    []string
	Markers []string
}
type Options struct {
	Scene           scene.Options
	BudgetExhausted *bool
}

func constant(profile scene.Profile, name string) int32 {
	for _, c := range gen.LayoutConst {
		if c.Name == profile.String()+"."+name {
			return c.Value
		}
	}
	return 0
}
func LayoutFamily(in Input, opts Options) (scene.Scene, error) {
	s := scene.Scene{Dump: scene.Dump{Kind: in.Kind, Options: opts.Scene}}
	g, lines, err := measuredGraph(in, opts.Scene)
	if err != nil {
		return s, err
	}
	if _, err = BreakCycles(g); err != nil {
		return s, err
	}
	parts, err := Components(g)
	if err != nil {
		return s, err
	}
	s.Boxes = slices.Clone(in.Boxes)
	s.Routes = slices.Clone(in.Routes)
	var cursor int32
	for _, members := range parts {
		cg, indices := rankComponentGraph(g, members)
		boxes, routes, budget, e := componentLayout(cg)
		if e != nil {
			return s, e
		}
		if budget && opts.BudgetExhausted != nil {
			*opts.BudgetExhausted = true
		}
		width, height := placeComponent(&s, in, indices, cg, boxes, routes, cursor)
		if int64(cursor)+int64(width)+int64(g.NodeGap) > math.MaxInt32 {
			return s, geom.ErrOverflow
		}
		cursor += width + g.NodeGap
		s.Canvas.W = cursor - g.NodeGap
		s.Canvas.H = max(s.Canvas.H, height)
	}
	orientScene(&s)
	assembleScene(&s, lines, in.Markers)
	return s, nil
}
func measuredGraph(in Input, o scene.Options) (*Graph, [][]measure.Line, error) {
	p, err := DefaultParams(o.Profile)
	if err != nil {
		return nil, nil, err
	}
	g := &Graph{Params: p}
	lines := make([][]measure.Line, len(in.Boxes))
	metric := measure.ForRole(measure.RoleLabel)
	if o.Profile == scene.ProfileCell {
		metric = measure.CellMetric()
	}
	for i, b := range in.Boxes {
		text := b.ID
		if i < len(in.Text) {
			text = in.Text[i]
		}
		ls, e := measure.Wrap(text, measure.WrapTarget(metric.Profile, 0, o.MaxWidth), metric)
		if e != nil {
			return nil, nil, e
		}
		lines[i] = ls
		n, err := measuredNode(b.ID, int32(i), ls, o.Profile)
		if err != nil {
			return nil, nil, err
		}
		g.Nodes = append(g.Nodes, n)
	}
	for i, r := range in.Routes {
		a, b := nodeIndex(g, r.From), nodeIndex(g, r.To)
		if a < 0 || b < 0 {
			return nil, nil, ErrGraph
		}
		g.Edges = append(g.Edges, Edge{Tail: a, Head: b, MinLen: 1, Decl: int32(i)})
	}
	sizePorts(g)
	orientSizes(g, o.Direction)
	return g, lines, nil
}

func orientSizes(g *Graph, direction scene.Direction) {
	if direction != scene.DirectionLR && direction != scene.DirectionRL {
		return
	}
	for i := range g.Nodes {
		g.Nodes[i].W, g.Nodes[i].H = g.Nodes[i].H, g.Nodes[i].W
	}
}

func measuredNode(id string, decl int32, lines []measure.Line, profile scene.Profile) (Node, error) {
	var tw int32
	for _, l := range lines {
		tw = max(tw, l.Width)
	}
	w := int64(tw) + 2*int64(constant(profile, "node_pad_x")) + 2*int64(constant(profile, "node_border"))
	h := int64(len(lines))*int64(constant(profile, "line_h")) + 2*int64(constant(profile, "node_pad_y")) + 2*int64(constant(profile, "node_border"))
	if w > math.MaxInt32 || h > math.MaxInt32 {
		return Node{}, geom.ErrOverflow
	}
	return Node{ID: id, Decl: decl, W: max(int32(w), constant(profile, "node_min_w")), H: max(int32(h), constant(profile, "node_min_h"))}, nil
}
func nodeIndex(g *Graph, id string) int32 {
	for i, n := range g.Nodes {
		if n.ID == id {
			return int32(i)
		}
	}
	return -1
}
func sizePorts(g *Graph) {
	for i := range g.Nodes {
		top, bottom := map[int32]bool{}, map[int32]bool{}
		for _, e := range g.Edges {
			if e.Head == int32(i) {
				top[e.Tail] = true
			}
			if e.Tail == int32(i) {
				bottom[e.Head] = true
			}
		}
		g.Nodes[i].W = max(g.Nodes[i].W, int32(max(len(top), len(bottom))+1)*g.PortGap)
	}
}
func componentLayout(g *Graph) ([]Box, []EdgeRoute, bool, error) {
	rank, e := RankWithBudget(g)
	if e != nil {
		return nil, nil, false, e
	}
	p, e := Normalize(g, rank.Ranks)
	if e != nil {
		return nil, nil, false, e
	}
	order, e := OrderWithBudget(p, OrderOptions{})
	if e != nil {
		return nil, nil, false, e
	}
	x, e := CrossCoords(p, order.Layers)
	if e != nil {
		return nil, nil, false, e
	}
	routing, e := Route(p, order.Layers, x)
	if e != nil {
		return nil, nil, false, e
	}
	y, top, e := RankCoords(p, order.Layers, routing)
	if e != nil {
		return nil, nil, false, e
	}
	routes, _, e := RoutePoints(p, order.Layers, x, y, top, routing)
	boxes := make([]Box, len(g.Nodes))
	for i, n := range g.Nodes {
		boxes[i] = Box{ID: n.ID, Rect: geom.Rect{X: x[i] - n.W/2, Y: y[i], W: n.W, H: n.H}}
	}
	return boxes, routes, rank.BudgetExhausted || order.BudgetExhausted, e
}
func placeComponent(s *scene.Scene, in Input, indices []int32, g *Graph, boxes []Box, routes []EdgeRoute, cursor int32) (int32, int32) {
	var minX, minY int32
	var right, bottom int32
	for i, b := range boxes {
		if i == 0 {
			minX, minY = b.Rect.X, b.Rect.Y
		}
		minX = min(minX, b.Rect.X)
		minY = min(minY, b.Rect.Y)
		right = max(right, b.Rect.X+b.Rect.W)
		bottom = max(bottom, b.Rect.Y+b.Rect.H)
	}
	for _, route := range routes {
		for _, p := range route.Points {
			minX, minY = min(minX, p.X), min(minY, p.Y)
			right, bottom = max(right, p.X), max(bottom, p.Y)
		}
	}
	for i, b := range boxes {
		r := b.Rect
		r.X += cursor - minX
		r.Y -= minY
		s.Boxes[indices[i]].Rect = r
	}
	for i, e := range g.Edges {
		original := int(e.Decl)
		points := slices.Clone(routes[i].Points)
		if e.Reversed {
			slices.Reverse(points)
		}
		for j := range points {
			points[j].X += cursor - minX
			points[j].Y -= minY
		}
		s.Routes[original].Points = points
	}
	return right - minX, bottom - minY
}
func orientPoint(p geom.Point, d scene.Direction, w, h int32) geom.Point {
	switch d {
	case scene.DirectionBT:
		p.Y = h - p.Y
	case scene.DirectionLR:
		p.X, p.Y = p.Y, p.X
	case scene.DirectionRL:
		p.X, p.Y = h-p.Y, p.X
	}
	return p
}
func orientScene(s *scene.Scene) {
	d := s.Options.Direction
	w, h := s.Canvas.W, s.Canvas.H
	for i := range s.Boxes {
		r := &s.Boxes[i].Rect
		p := orientPoint(geom.Point{X: r.X, Y: r.Y}, d, w, h)
		switch d {
		case scene.DirectionBT:
			p.Y -= r.H
		case scene.DirectionLR:
			r.W, r.H = r.H, r.W
		case scene.DirectionRL:
			r.W, r.H = r.H, r.W
			p.X -= r.W
		}
		r.X, r.Y = p.X, p.Y
	}
	for i := range s.Routes {
		for j, p := range s.Routes[i].Points {
			s.Routes[i].Points[j] = orientPoint(p, d, w, h)
		}
	}
	if d == scene.DirectionLR || d == scene.DirectionRL {
		s.Canvas.W, s.Canvas.H = h, w
	}
}
func assembleScene(s *scene.Scene, lines [][]measure.Line, markers []string) {
	for i, r := range s.Routes {
		items := []scene.Primitive{&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Points: r.Points, Corner: constant(s.Options.Profile, "corner_radius")}}
		if i < len(markers) && markers[i] != "" && len(r.Points) > 1 {
			end := len(r.Points) - 1
			items = append(items, &scene.MarkerRef{Marker: markers[i], At: r.Points[end], Axis: markerAxis(r.Points[end-1], r.Points[end])})
		}
		s.Groups = append(s.Groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: r.ID, Items: items})
	}
	for i, b := range s.Boxes {
		lh := constant(s.Options.Profile, "line_h")
		rect := b.Rect
		rect.H = int32(len(lines[i])) * lh
		rect.Y += (b.Rect.H - rect.H) / 2
		runs := make([][]scene.Run, len(lines[i]))
		for j, l := range lines[i] {
			runs[j] = []scene.Run{{Text: l.Text}}
		}
		s.Groups = append(s.Groups, &scene.Group{Role: scene.GroupRoleNode, Owner: b.ID, Items: []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: b.Rect}, &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: runs}}})
	}
}

func markerAxis(a, b geom.Point) scene.Axis {
	dx, dy := int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y)
	if abs64(dx) >= abs64(dy) {
		if dx < 0 {
			return scene.AxisMinusX
		}
		return scene.AxisPlusX
	}
	if dy < 0 {
		return scene.AxisMinusY
	}
	return scene.AxisPlusY
}
func abs64(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}
