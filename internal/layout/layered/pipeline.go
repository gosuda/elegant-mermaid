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
	Kind   string
	Boxes  []scene.Box
	Routes []scene.Route
	Labels []scene.Label
	Text   []string
	Edges  []EdgeOptions
	Fixed  []FixedGroup
}
type GroupOptions struct{ ID, Direction string }
type FixedGroup struct {
	ID      string
	Scene   scene.Scene
	W, H    int32
	Title   geom.Rect
	Titles  []Box
	packing packingReservations
}
type EdgeOptions struct {
	MarkerStart, MarkerEnd, Stroke string
	MinLength                      int32
}
type Options struct {
	Scene             scene.Options
	BudgetExhausted   *bool
	IgnoredDirections *[]string
	capturePacking    *packingReservations
}
type scenePreparation struct {
	input  Input
	layout Layout
	lines  [][]measure.Line
}
type packingReservations struct {
	loops  []Box
	labels []LabelReservation
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
	if err := enforceLimits(in, opts.Scene); err != nil {
		return s, err
	}
	prepared, err := prepareSubgraphs(in, opts)
	if err != nil {
		return s, err
	}
	g, lines, err := measuredGraph(prepared, opts.Scene)
	if err != nil {
		return s, err
	}
	part, err := layoutComponents(g, int(opts.Scene.Thoroughness))
	if err != nil {
		return s, err
	}
	if opts.capturePacking != nil {
		*opts.capturePacking = packingReservations{loops: part.Extents, labels: part.LabelReservations}
	}
	s, err = layoutScene(in, opts.Scene, scenePreparation{input: prepared, layout: part, lines: lines})
	projectFinalScene(&s, opts, err)
	if part.BudgetExhausted && opts.BudgetExhausted != nil {
		*opts.BudgetExhausted = true
	}
	return s, err
}
func layoutScene(in Input, o scene.Options, prepared scenePreparation) (scene.Scene, error) {
	s := scene.Scene{Dump: scene.Dump{Kind: in.Kind, Options: o}}
	s.Boxes = slices.Clone(in.Boxes)
	s.Routes = slices.Clone(in.Routes)
	s.Labels = slices.Clone(in.Labels)
	applyLayout(&s, prepared.layout)
	orientScene(&s)
	if err := addMargin(&s, constant(o.Profile, "canvas_margin")); err != nil {
		return s, err
	}
	lines := prepared.lines
	if len(prepared.input.Fixed) > 0 {
		var err error
		lines, err = allBoxLines(in, o)
		if err != nil {
			return s, err
		}
	}
	if err := fillLabelLines(&s, o); err != nil {
		return s, err
	}
	titles, err := sceneTitles(prepared.layout, o)
	if err != nil {
		return s, err
	}
	assembleScene(&s, lines, in.Edges, titles)
	return s, nil
}
func layoutComponents(g *Graph, thoroughness int) (Layout, error) {
	parts, err := Components(g)
	if err != nil {
		return Layout{}, err
	}
	layouts := make([]Layout, 0, len(parts))
	for _, members := range parts {
		cg, _ := rankComponentGraph(g, members)
		part, err := Portfolio(cg, thoroughness)
		if err != nil {
			return Layout{}, err
		}
		layouts = append(layouts, part)
	}
	return Pack(layouts, PackOptions{MaxWidth: g.MaxWidth, Gap: g.NodeGap, AspectNum: g.AspectNum, AspectDen: g.AspectDen})
}
func applyLayout(s *scene.Scene, part Layout) {
	s.Canvas = geom.Size{W: part.Width, H: part.Height}
	for i := range s.Boxes {
		s.Boxes[i].Rect = findBox(part.Boxes, s.Boxes[i].ID)
	}
	for _, r := range part.Routes {
		for i := range s.Routes {
			if s.Routes[i].ID == r.ID {
				s.Routes[i].Points = r.Points
			}
		}
	}
	for i := range s.Labels {
		s.Labels[i].Rect = findBox(part.Labels, s.Labels[i].ID)
		for _, b := range s.Boxes {
			if b.ID == s.Labels[i].Owner && b.Role == scene.RoleGroup {
				s.Labels[i].Rect = findBox(part.Titles, b.ID)
			}
		}
	}
}
func metricFor(profile scene.Profile) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.ForRole(measure.RoleLabel)
}
func allBoxLines(in Input, o scene.Options) ([][]measure.Line, error) {
	lines := make([][]measure.Line, len(in.Boxes))
	for i := range in.Boxes {
		text := inputBoxText(in, i)
		ls, err := wrapLabel(text, o)
		if err != nil {
			return nil, err
		}
		lines[i] = ls
	}
	return lines, nil
}
func measuredGraph(in Input, o scene.Options) (*Graph, [][]measure.Line, error) {
	if err := enforceLimits(in, o); err != nil {
		return nil, nil, err
	}
	p, err := DefaultParams(o.Profile)
	if err != nil {
		return nil, nil, err
	}
	if o.Profile == scene.ProfileCell {
		p.MaxWidth = o.MaxWidth
	}
	g := &Graph{Params: p, Fixed: in.Fixed, Direction: o.Direction}
	lines, err := allBoxLines(in, o)
	if err != nil {
		return nil, nil, err
	}
	if err := populateNodes(g, in, o, lines); err != nil {
		return nil, nil, err
	}
	clusterRankNodes(g)
	if err := graphEdges(g, in, o); err != nil {
		return nil, nil, err
	}
	orientSizes(g, o.Direction)
	if err := sizeLoops(g); err != nil {
		return nil, nil, err
	}
	if err := sizeFrameLoops(g); err != nil {
		return nil, nil, err
	}
	clusterRankEdges(g)
	return g, lines, nil
}
func populateNodes(g *Graph, in Input, o scene.Options, lines [][]measure.Line) error {
	for i, b := range in.Boxes {
		if b.Role == scene.RoleGroup && fixedGroup(in.Fixed, b.ID) == nil {
			title, err := measuredTitle(lines[i], o)
			if err != nil {
				return err
			}
			g.Clusters = append(g.Clusters, Cluster{ID: b.ID, Parent: b.Parent, Decl: int32(i), Lines: lines[i], TitleSize: title})
			continue
		}
		node, err := measuredNode(b.ID, int32(i), lines[i], o.Profile)
		if err != nil {
			return err
		}
		node.Parent = b.Parent
		node.Role = b.Role
		if fixed := fixedGroup(in.Fixed, b.ID); fixed != nil {
			node.W = fixed.W
			node.H = fixed.H
		}
		g.Nodes = append(g.Nodes, node)
	}
	return nil
}
func graphEdges(g *Graph, in Input, o scene.Options) error {
	for i, r := range in.Routes {
		edge, err := modelEdge(g, in, r)
		if err != nil {
			return err
		}
		label, err := measureEdgeLabel(in, r.ID, o)
		if err != nil {
			return err
		}
		length := int32(1)
		if label != nil {
			length = 2
		}
		edge.ID = r.ID
		edge.MinLen = length
		edge.Decl = int32(i)
		edge.Label = label
		g.Edges = append(g.Edges, edge)
	}
	return nil
}
func measureEdgeLabel(in Input, owner string, o scene.Options) (*EdgeLabel, error) {
	var aggregate EdgeLabel
	for _, label := range in.Labels {
		if label.Owner != owner {
			continue
		}
		item, err := measureLabel(label, o)
		if err != nil {
			return nil, err
		}
		if err := aggregate.append(item, constant(o.Profile, "slot")); err != nil {
			return nil, err
		}
	}
	if len(aggregate.Items) == 0 {
		return nil, nil
	}
	return &aggregate, nil
}
func measureLabel(label scene.Label, o scene.Options) (MeasuredLabel, error) {
	lines, err := wrapLabel(label.Text, o)
	if err != nil {
		return MeasuredLabel{}, err
	}
	height, err := coordinate(int64(len(lines)) * int64(constant(o.Profile, "line_h")))
	if err != nil {
		return MeasuredLabel{}, err
	}
	item := MeasuredLabel{ID: label.ID, Text: label.Text, H: height, Lines: lines}
	for _, line := range lines {
		item.W = max(item.W, line.Width)
	}
	if o.Direction == scene.DirectionLR || o.Direction == scene.DirectionRL {
		item.W, item.H = item.H, item.W
	}
	return item, nil
}
func (label *EdgeLabel) append(item MeasuredLabel, slot int32) error {
	height := int64(label.H) + int64(item.H)
	if len(label.Items) > 0 {
		height += int64(slot)
	}
	h, err := coordinate(height)
	if err != nil {
		return err
	}
	label.W = max(label.W, item.W)
	label.H = h
	label.Items = append(label.Items, item)
	return nil
}
func orientSizes(g *Graph, d scene.Direction) {
	if d != scene.DirectionLR && d != scene.DirectionRL {
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
func orientRect(r geom.Rect, d scene.Direction, w, h int32) geom.Rect {
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
	return r
}
func orientScene(s *scene.Scene) {
	d := s.Options.Direction
	w, h := s.Canvas.W, s.Canvas.H
	for i := range s.Boxes {
		s.Boxes[i].Rect = orientRect(s.Boxes[i].Rect, d, w, h)
	}
	for i := range s.Labels {
		s.Labels[i].Rect = orientRect(s.Labels[i].Rect, d, w, h)
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
func addMargin(s *scene.Scene, margin int32) error {
	part := Layout{}
	for _, b := range s.Boxes {
		part.Boxes = append(part.Boxes, Box{ID: b.ID, Rect: b.Rect})
	}
	for _, l := range s.Labels {
		part.Labels = append(part.Labels, Box{ID: l.ID, Rect: l.Rect})
	}
	for i, r := range s.Routes {
		part.Routes = append(part.Routes, EdgeRoute{Original: int32(i), Points: r.Points})
	}
	if err := translateLayout(&part, int64(margin), int64(margin)); err != nil {
		return err
	}
	w, err := coordinate(int64(s.Canvas.W) + 2*int64(margin))
	if err != nil {
		return err
	}
	h, err := coordinate(int64(s.Canvas.H) + 2*int64(margin))
	if err != nil {
		return err
	}
	for i := range s.Boxes {
		s.Boxes[i].Rect = part.Boxes[i].Rect
	}
	for i := range s.Labels {
		s.Labels[i].Rect = part.Labels[i].Rect
	}
	for i := range s.Routes {
		s.Routes[i].Points = part.Routes[i].Points
	}
	s.Canvas = geom.Size{W: w, H: h}
	return nil
}
func fillLabelLines(s *scene.Scene, o scene.Options) error {
	for i := range s.Labels {
		lines, err := wrapLabel(s.Labels[i].Text, o)
		if err != nil {
			return err
		}
		s.Labels[i].Lines = make([]string, 0, len(lines))
		for _, l := range lines {
			s.Labels[i].Lines = append(s.Labels[i].Lines, l.Text)
		}
	}
	return nil
}
func assembleScene(s *scene.Scene, lines [][]measure.Line, edges []EdgeOptions, titles []Box) {
	for i, b := range s.Boxes {
		if b.Role == scene.RoleGroup {
			s.Groups = append(s.Groups, clusterGroup(s, b, lines[i], titles))
		}
	}
	for i, r := range s.Routes {
		options := EdgeOptions{}
		if i < len(edges) {
			options = edges[i]
		}
		group := &scene.Group{Role: scene.GroupRoleEdge, Owner: r.ID, Items: edgeItems(r, options, s.Options.Profile)}
		for _, l := range s.Labels {
			if l.Owner == r.ID {
				group.Items = append(group.Items, labelPrimitive(l, s.Options.Profile))
			}
		}
		s.Groups = append(s.Groups, group)
	}
	for i, b := range s.Boxes {
		if b.Role == scene.RoleNode {
			s.Groups = append(s.Groups, boxGroup(b, lines[i], s.Options.Profile))
		}
	}
}
func textRuns(lines []measure.Line) [][]scene.Run {
	runs := make([][]scene.Run, len(lines))
	for i, l := range lines {
		runs[i] = []scene.Run{{Text: l.Text}}
	}
	return runs
}
func clusterGroup(s *scene.Scene, b scene.Box, lines []measure.Line, titles []Box) *scene.Group {
	group := boxGroup(b, lines, s.Options.Profile)
	text, ok := group.Items[1].(*scene.Text)
	if ok {
		text.Rect = findBox(titles, b.ID)
	}
	return group
}
func boxGroup(b scene.Box, lines []measure.Line, p scene.Profile) *scene.Group {
	role, style := scene.GroupRoleNode, "node"
	rect := b.Rect
	rect.H = int32(len(lines)) * constant(p, "line_h")
	if b.Role == scene.RoleGroup {
		role = scene.GroupRoleGroup
		style = "group"
		rect.Y += constant(p, "cluster_pad")
	} else {
		rect.Y += (b.Rect.H - rect.H) / 2
	}
	return &scene.Group{Role: role, Owner: b.ID, Items: []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: style}, Rect: b.Rect}, &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: textRuns(lines)}}}
}
func labelPrimitive(l scene.Label, p scene.Profile) *scene.Text {
	lines := make([][]scene.Run, len(l.Lines))
	for i, text := range l.Lines {
		lines[i] = []scene.Run{{Text: text}}
	}
	return &scene.Text{Rect: l.Rect, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: lines}
}
func edgeItems(route scene.Route, options EdgeOptions, profile scene.Profile) []scene.Primitive {
	if options.Stroke == "invisible" {
		return nil
	}
	shape := scene.Shape{Style: "edge"}
	switch options.Stroke {
	case "thick":
		shape.Width.Kind = scene.WidthEmphasis
	case "dotted":
		shape.Line = scene.LineDotted
	case "dashed":
		shape.Line = scene.LineDashed
	}
	items := []scene.Primitive{&scene.Polyline{Shape: shape, Points: route.Points, Corner: constant(profile, "corner_radius")}}
	if len(route.Points) < 2 {
		return items
	}
	end := len(route.Points) - 1
	if options.MarkerStart != "" {
		items = append(items, &scene.MarkerRef{Marker: options.MarkerStart, At: route.Points[0], Axis: markerAxis(route.Points[1], route.Points[0])})
	}
	if options.MarkerEnd != "" {
		items = append(items, &scene.MarkerRef{Marker: options.MarkerEnd, At: route.Points[end], Axis: markerAxis(route.Points[end-1], route.Points[end])})
	}
	return items
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
