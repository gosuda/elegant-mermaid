package layered

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func RerouteEndpoints(in Input, s scene.Scene) (scene.Scene, error) {
	if !hasForcedSides(in.Edges) {
		return s, nil
	}
	g, err := rerouteGraph(in, s.Options)
	if err != nil {
		return scene.Scene{}, err
	}
	boxes, err := sceneNodeRects(s, g.Nodes)
	if err != nil {
		return scene.Scene{}, err
	}
	search := forcedSearch{
		in:     in,
		g:      g,
		boxes:  boxes,
		labels: sceneTextRects(s),
		bound:  geom.Rect{W: s.Canvas.W, H: s.Canvas.H},
	}
	out := s
	out.Routes = slices.Clone(s.Routes)
	out.Groups = cloneGroups(s.Groups)
	for i := range in.Routes {
		if err := rerouteRoute(&search, &out, i); err != nil {
			return scene.Scene{}, err
		}
	}
	if out.Options.Profile != scene.ProfileCell {
		return out, nil
	}
	canvas, err := cellCanvasFitting(out.Canvas, out.Routes)
	if err != nil {
		return scene.Scene{}, err
	}
	out.Canvas = canvas
	return out, nil
}

func cellCanvasFitting(canvas geom.Size, routes []scene.Route) (geom.Size, error) {
	w, h := int64(canvas.W), int64(canvas.H)
	for _, route := range routes {
		for _, p := range route.Points {
			w, h = max(w, int64(p.X)+1), max(h, int64(p.Y)+1)
		}
	}
	fitW, err := coordinate(w)
	if err != nil {
		return geom.Size{}, err
	}
	fitH, err := coordinate(h)
	return geom.Size{W: fitW, H: fitH}, err
}

type forcedSearch struct {
	in     Input
	g      *Graph
	boxes  []geom.Rect
	labels []geom.Rect
	bound  geom.Rect
}

func (f *forcedSearch) route(edge *Edge, fromSide, toSide geom.Side) ([]geom.Point, error) {
	obstacles := append(endpointObstacles(f.in, f.g, f.boxes, edge), f.labels...)
	starts, err := endpointPorts(f.boxes[edge.Tail])
	if err != nil {
		return nil, err
	}
	ends, err := endpointPorts(f.boxes[edge.Head])
	if err != nil {
		return nil, err
	}
	source, err := forcedPort(starts, fromSide)
	if err != nil {
		return nil, err
	}
	target, err := forcedPort(ends, toSide)
	if err != nil {
		return nil, err
	}
	searchStarts, searchEnds := sideSearchPoints(starts, source), sideSearchPoints(ends, target)
	grid, err := newVisibilityGrid(obstacles, searchStarts, searchEnds, f.bound)
	if err != nil {
		return nil, err
	}
	if err := grid.checkStub(source); err != nil {
		return nil, err
	}
	if err := grid.checkStub(target); err != nil {
		return nil, err
	}
	points, err := grid.shortest(searchStarts, searchEnds)
	if err != nil {
		return nil, err
	}
	return joinStubs(points, source, target), nil
}

func rerouteRoute(search *forcedSearch, out *scene.Scene, i int) error {
	edge := edgeOptionsAt(search.in.Edges, i)
	if edge.FromSide == geom.SideNone && edge.ToSide == geom.SideNone {
		return nil
	}
	if i >= len(search.g.Edges) || search.g.Edges[i].Decl != int32(i) {
		return ErrGraph
	}
	points, err := search.route(&search.g.Edges[i], edge.FromSide, edge.ToSide)
	if err != nil {
		return err
	}
	group := edgeGroup(out.Groups, search.in.Routes[i].ID)
	if group == nil {
		return ErrGraph
	}
	if err := updateEdgeGroup(group, points, edge); err != nil {
		return err
	}
	out.Routes[i].Points = points
	return nil
}

func rerouteGraph(in Input, o scene.Options) (*Graph, error) {
	p, err := DefaultParams(o.Profile)
	if err != nil {
		return nil, err
	}
	g := &Graph{Params: p, Direction: o.Direction}
	metric := metricFor(o.Profile).WithFontFamily(o.FontFamily)
	target := int32(0)
	if o.Profile == scene.ProfileCell {
		target = o.MaxWidth
	}
	for i := range in.Boxes {
		ls, err := measure.StyledLines(inputBoxText(in, i), measure.WrapTarget(metric.Profile, 0, target), metric)
		if err != nil {
			return nil, err
		}
		node, err := rerouteNode(in, i, ls, o)
		if err != nil {
			return nil, err
		}
		g.Nodes = append(g.Nodes, node)
	}
	for i := range in.Routes {
		edge, err := rerouteEdge(g, in, i)
		if err != nil {
			return nil, err
		}
		g.Edges = append(g.Edges, edge)
	}
	orientSizes(g, o.Direction)
	return g, nil
}

func rerouteNode(in Input, i int, ls []measure.StyledLine, o scene.Options) (Node, error) {
	w, h, err := measuredContent(ls, o.Profile)
	if err != nil {
		return Node{}, err
	}
	contentW, contentH := w, h
	if i < len(in.Sizes) && in.Sizes[i] != (geom.Size{}) {
		contentW, contentH = in.Sizes[i].W, in.Sizes[i].H
	}
	if contentW < 0 || contentH < 0 {
		return Node{}, ErrGraph
	}
	node := Node{ID: in.Boxes[i].ID, Decl: int32(i)}
	if in.Boxes[i].Role == scene.RoleGroup {
		node.W, err = textWidth(ls)
		if err != nil {
			return Node{}, err
		}
		node.H, err = coordinate(int64(max(len(ls), 1)) * int64(constant(o.Profile, "line_h")))
		return node, err
	}
	node.W = max(contentW, constant(o.Profile, "node_min_w"))
	node.H = max(contentH, constant(o.Profile, "node_min_h"))
	return node, nil
}

func measuredContent(ls []measure.StyledLine, profile scene.Profile) (int32, int32, error) {
	tw, err := textWidth(ls)
	if err != nil {
		return 0, 0, err
	}
	w, err := coordinate(int64(tw) + 2*int64(constant(profile, "node_pad_x")) + 2*int64(constant(profile, "node_border")))
	if err != nil {
		return 0, 0, err
	}
	h, err := coordinate(int64(len(ls))*int64(constant(profile, "line_h")) + 2*int64(constant(profile, "node_pad_y")) + 2*int64(constant(profile, "node_border")))
	return w, h, err
}

func textWidth(ls []measure.StyledLine) (int32, error) {
	var width int32
	for _, line := range ls {
		width = max(width, line.Width)
	}
	return coordinate(int64(width))
}

func rerouteEdge(g *Graph, in Input, i int) (Edge, error) {
	tail := nodeIndex(g, in.Routes[i].From)
	head := nodeIndex(g, in.Routes[i].To)
	if tail < 0 || head < 0 {
		return Edge{}, ErrGraph
	}
	length := edgeOptionsAt(in.Edges, i).MinLength
	if hasRouteLabel(in, in.Routes[i].ID) {
		length = max(length, 2)
	} else {
		length = max(length, 1)
	}
	return Edge{Tail: tail, Head: head, MinLen: length, Decl: int32(i)}, nil
}

func endpointObstacles(in Input, g *Graph, boxes []geom.Rect, edge *Edge) []geom.Rect {
	hidden := endpointAncestors(in, g.Nodes[edge.Tail].ID)
	hidden = append(hidden, endpointAncestors(in, g.Nodes[edge.Head].ID)...)
	var out []geom.Rect
	for i, node := range g.Nodes {
		if node.Decl < 0 || int(node.Decl) >= len(in.Boxes) {
			continue
		}
		decl := int(node.Decl)
		if in.Boxes[decl].Exclusive && !slices.Contains(hidden, decl) {
			out = append(out, boxes[i])
		}
	}
	return out
}

func endpointAncestors(in Input, id string) []int {
	var out []int
	parent := inputParent(in, id)
	for fuel := 64; parent != "" && fuel > 0; fuel-- {
		index := inputBoxIndex(in, parent)
		if index < 0 {
			break
		}
		out = append(out, index)
		parent = in.Boxes[index].Parent
	}
	return out
}

func inputBoxIndex(in Input, id string) int {
	for i := range in.Boxes {
		if in.Boxes[i].ID == id {
			return i
		}
	}
	return -1
}

func joinStubs(points, source, target []geom.Point) []geom.Point {
	if source != nil {
		points = append([]geom.Point{source[0]}, points...)
	}
	if target != nil {
		points = append(points, target[0])
	}
	return points
}

func updateEdgeGroup(group *scene.Group, points []geom.Point, edge EdgeOptions) error {
	if len(points) == 0 {
		return ErrGraph
	}
	markerIndex := 0
	for i, item := range group.Items {
		switch primitive := item.(type) {
		case *scene.Polyline:
			line := *primitive
			line.Points = points
			group.Items[i] = &line
		case *scene.MarkerRef:
			marker, err := reroutedMarker(primitive, points, edge, markerIndex)
			if err != nil {
				return err
			}
			group.Items[i] = marker
			markerIndex++
		}
	}
	return nil
}

func reroutedMarker(marker *scene.MarkerRef, points []geom.Point, edge EdgeOptions, index int) (*scene.MarkerRef, error) {
	a, b, err := markerStubs(points, edge, index)
	if err != nil {
		return nil, err
	}
	updated := *marker
	updated.At = b
	updated.Axis = sideAxis(a, b)
	return &updated, nil
}

func markerStubs(points []geom.Point, edge EdgeOptions, index int) (geom.Point, geom.Point, error) {
	if index == 0 && edge.MarkerStart != "" {
		return startMarkerEnds(points)
	}
	return endMarkerEnds(points, len(points)-1)
}

func startMarkerEnds(points []geom.Point) (geom.Point, geom.Point, error) {
	if len(points) < 2 {
		return geom.Point{}, geom.Point{}, ErrGraph
	}
	return points[1], points[0], nil
}

func endMarkerEnds(points []geom.Point, end int) (geom.Point, geom.Point, error) {
	if end < 1 {
		return geom.Point{}, geom.Point{}, ErrGraph
	}
	return points[end-1], points[end], nil
}

func sideAxis(a, b geom.Point) scene.Axis {
	if b.X < a.X {
		return scene.AxisMinusX
	}
	if b.X > a.X {
		return scene.AxisPlusX
	}
	if b.Y < a.Y {
		return scene.AxisMinusY
	}
	return scene.AxisPlusY
}

func hasForcedSides(edges []EdgeOptions) bool {
	for _, edge := range edges {
		if edge.FromSide != geom.SideNone || edge.ToSide != geom.SideNone {
			return true
		}
	}
	return false
}

func edgeOptionsAt(edges []EdgeOptions, i int) EdgeOptions {
	if i < len(edges) {
		return edges[i]
	}
	return EdgeOptions{}
}

func hasRouteLabel(in Input, id string) bool {
	for _, label := range in.Labels {
		if label.Owner == id {
			return true
		}
	}
	return false
}

func sceneNodeRects(s scene.Scene, nodes []Node) ([]geom.Rect, error) {
	rects := make([]geom.Rect, len(nodes))
	for i, node := range nodes {
		rect, ok := sceneRect(s, node.ID)
		if !ok {
			return nil, ErrGraph
		}
		rects[i] = rect
	}
	return rects, nil
}

func sceneRect(s scene.Scene, id string) (geom.Rect, bool) {
	for _, box := range s.Boxes {
		if box.ID == id {
			return box.Rect, true
		}
	}
	return geom.Rect{}, false
}

func sceneTextRects(s scene.Scene) []geom.Rect {
	var rects []geom.Rect
	for _, group := range s.Groups {
		for _, item := range group.Items {
			if text, ok := item.(*scene.Text); ok {
				rects = append(rects, text.Rect)
			}
		}
	}
	return rects
}

func cloneGroups(groups []*scene.Group) []*scene.Group {
	out := make([]*scene.Group, len(groups))
	for i, group := range groups {
		clone := *group
		clone.Items = slices.Clone(group.Items)
		out[i] = &clone
	}
	return out
}

func edgeGroup(groups []*scene.Group, owner string) *scene.Group {
	for _, group := range groups {
		if group.Role == scene.GroupRoleEdge && group.Owner == owner {
			return group
		}
	}
	return nil
}
