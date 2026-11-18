package layered

import (
	"math"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type Input struct {
	Kind        string
	Boxes       []scene.Box
	Routes      []scene.Route
	Labels      []scene.Label
	Text        []string
	Edges       []EdgeOptions
	Fixed       []FixedGroup
	Sizes       []geom.Size
	Exact       []bool
	Attachments []Attachment
	RegionSets  []RegionSet
}
type (
	GroupOptions struct{ ID, Direction string }
	FixedGroup   struct {
		ID      string
		Scene   scene.Scene
		W, H    int32
		Title   geom.Rect
		Titles  []Box
		packing packingReservations
	}
)

type EdgeOptions struct {
	MarkerStart, MarkerEnd, Stroke string
	MinLength                      int32
	FromSide, ToSide               geom.Side
}
type Options struct {
	Scene             scene.Options
	BudgetExhausted   *bool
	IgnoredDirections *[]string
	capturePacking    *packingReservations
}
type scenePreparation struct {
	layout    Layout
	labelRuns map[string][][]scene.Run
	boxRuns   map[string][][]scene.Run
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
	if err := validateAttachments(in); err != nil {
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
	s, err = layoutScene(in, opts.Scene, scenePreparation{layout: part, boxRuns: measuredBoxRuns(prepared, lines), labelRuns: measuredLabelRuns(g, prepared, lines)})
	if err == nil {
		err = lowerVectorMath(&s, g, prepared, lines)
	}
	if part.BudgetExhausted && opts.BudgetExhausted != nil {
		*opts.BudgetExhausted = true
	}
	return s, err
}

func lowerVectorMath(s *scene.Scene, g *Graph, in Input, lines [][]measure.StyledLine) error {
	if s.Options.Profile != scene.ProfileVector {
		return nil
	}
	boxes, labels := measuredMathLines(g, in, lines)
	return lowerMeasuredMath(s, boxes, labels)
}

func layoutScene(in Input, o scene.Options, prepared scenePreparation) (scene.Scene, error) {
	s := scene.Scene{Dump: scene.Dump{Kind: in.Kind, Options: o}}
	s.Boxes = slices.Clone(in.Boxes)
	s.Routes = slices.Clone(in.Routes)
	s.Labels = slices.Clone(in.Labels)
	applyLayout(&s, prepared.layout)
	orientScene(&s)
	margin := canvasMargin(o.Profile, in.Kind)
	if err := addMargin(&s, margin); err != nil {
		return s, err
	}
	lines := prepared.boxRuns
	fillLabelLines(&s, prepared.labelRuns)
	titles, err := sceneTitles(prepared.layout, o, margin)
	if err != nil {
		return s, err
	}
	assembleScene(&s, lines, in.Edges, titles, prepared.labelRuns)
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

func allBoxLines(in Input, o scene.Options) ([][]measure.StyledLine, error) {
	lines := make([][]measure.StyledLine, len(in.Boxes))
	for i := range in.Boxes {
		text := inputBoxText(in, i)
		ls, err := wrapLabel(text, in.Kind, o)
		if err != nil {
			return nil, err
		}
		lines[i] = ls
	}
	return lines, nil
}

func measuredParams(in Input, o scene.Options) (Params, error) {
	if err := enforceLimits(in, o); err != nil {
		return Params{}, err
	}
	p, err := DefaultParams(o.Profile)
	if err != nil {
		return Params{}, err
	}
	p.applyKindSpacing(o.Profile, in.Kind)
	if o.Profile == scene.ProfileCell {
		p.MaxWidth = o.MaxWidth
	}
	return p, nil
}

func measuredGraph(in Input, o scene.Options) (*Graph, [][]measure.StyledLine, error) {
	p, err := measuredParams(in, o)
	if err != nil {
		return nil, nil, err
	}
	g := &Graph{Params: p, Fixed: in.Fixed, Direction: o.Direction}
	if g.regions, err = graphRegions(in, o.Profile); err != nil {
		return nil, nil, err
	}
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
	if err := connectAttachments(g, in); err != nil {
		return nil, nil, err
	}
	return g, lines, nil
}

func populateNodes(g *Graph, in Input, o scene.Options, lines [][]measure.StyledLine) error {
	for i, b := range in.Boxes {
		if b.Role == scene.RoleGroup && fixedGroup(in.Fixed, b.ID) == nil {
			title, err := measuredTitle(lines[i], o)
			if err != nil {
				return err
			}
			g.Clusters = append(g.Clusters, Cluster{ID: b.ID, Parent: b.Parent, Decl: int32(i), Lines: lines[i], TitleSize: title})
			continue
		}
		node, err := inputNode(in, o, i, lines[i])
		if err != nil {
			return err
		}
		g.Nodes = append(g.Nodes, node)
	}
	return nil
}

func inputNode(in Input, o scene.Options, i int, lines []measure.StyledLine) (Node, error) {
	b := in.Boxes[i]
	node, err := measuredNode(b.ID, int32(i), lines, o.Profile)
	if err != nil {
		return Node{}, err
	}
	if err := applyInputSize(&node, in, i, o.Profile); err != nil {
		return Node{}, err
	}
	node.Parent = b.Parent
	node.Role = b.Role
	if fixed := fixedGroup(in.Fixed, b.ID); fixed != nil {
		node.W = fixed.W
		node.H = fixed.H
	}
	return node, nil
}

func applyInputSize(node *Node, in Input, i int, profile scene.Profile) error {
	if i < len(in.Exact) && in.Exact[i] && i < len(in.Sizes) {
		if in.Sizes[i].W < 0 || in.Sizes[i].H < 0 {
			return ErrGraph
		}
		node.W, node.H, node.Exact = in.Sizes[i].W, in.Sizes[i].H, true
		return nil
	}
	if i < len(in.Sizes) && in.Sizes[i] != (geom.Size{}) {
		node.W = max(in.Sizes[i].W, constant(profile, "node_min_w"))
		node.H = max(in.Sizes[i].H, constant(profile, "node_min_h"))
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
		length := max(edgeOptionsAt(in.Edges, i).MinLength, 1)
		if label != nil {
			length = max(length, 2)
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
		item, err := measureLabel(label, in.Kind, o)
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

func measureLabel(label scene.Label, kind string, o scene.Options) (MeasuredLabel, error) {
	lines, err := wrapLabel(label.Text, kind, o)
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

func measuredNode(id string, decl int32, lines []measure.StyledLine, profile scene.Profile) (Node, error) {
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

func orientPoint(p geom.Point, d scene.Direction, h int32) geom.Point {
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

func orientRect(r geom.Rect, d scene.Direction, h int32) geom.Rect {
	p := orientPoint(geom.Point{X: r.X, Y: r.Y}, d, h)
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
		s.Boxes[i].Rect = orientRect(s.Boxes[i].Rect, d, h)
	}
	for i := range s.Labels {
		s.Labels[i].Rect = orientRect(s.Labels[i].Rect, d, h)
	}
	for i := range s.Routes {
		for j, p := range s.Routes[i].Points {
			s.Routes[i].Points[j] = orientPoint(p, d, h)
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

func measuredBoxRuns(in Input, lines [][]measure.StyledLine) map[string][][]scene.Run {
	runs := make(map[string][][]scene.Run, len(in.Boxes))
	for i, box := range in.Boxes {
		runs[box.ID] = textRuns(lines[i])
	}
	for _, fixed := range in.Fixed {
		for _, group := range fixed.Scene.Groups {
			if group.Role != scene.GroupRoleNode && group.Role != scene.GroupRoleGroup {
				continue
			}
			for _, item := range group.Items {
				if text, ok := item.(*scene.Text); ok {
					runs[group.Owner] = text.Lines
					break
				}
			}
		}
	}
	return runs
}

func measuredLabelRuns(g *Graph, in Input, lines [][]measure.StyledLine) map[string][][]scene.Run {
	runs := make(map[string][][]scene.Run, len(in.Labels))
	for _, edge := range g.Edges {
		if edge.Label != nil {
			for _, item := range edge.Label.Items {
				runs[item.ID] = textRuns(item.Lines)
			}
		}
	}
	for _, label := range in.Labels {
		for i, box := range in.Boxes {
			if label.Owner == box.ID {
				runs[label.ID] = textRuns(lines[i])
			}
		}
	}
	for _, fixed := range in.Fixed {
		appendFixedLabelRuns(runs, fixed.Scene)
	}
	return runs
}

func appendFixedLabelRuns(runs map[string][][]scene.Run, s scene.Scene) {
	for _, group := range s.Groups {
		var labels []scene.Label
		for _, label := range s.Labels {
			if label.Owner == group.Owner {
				labels = append(labels, label)
			}
		}
		index := 0
		for _, item := range group.Items {
			text, ok := item.(*scene.Text)
			if !ok || index >= len(labels) {
				continue
			}
			runs[labels[index].ID] = text.Lines
			index++
		}
	}
}

func fillLabelLines(s *scene.Scene, runs map[string][][]scene.Run) {
	for i := range s.Labels {
		lines := runs[s.Labels[i].ID]
		s.Labels[i].Lines = make([]string, 0, len(lines))
		for _, line := range lines {
			var text strings.Builder
			for _, run := range line {
				text.WriteString(run.Text)
			}
			s.Labels[i].Lines = append(s.Labels[i].Lines, text.String())
		}
	}
}

func assembleScene(s *scene.Scene, lines map[string][][]scene.Run, edges []EdgeOptions, titles []Box, labelRuns map[string][][]scene.Run) {
	for _, b := range s.Boxes {
		if b.Role == scene.RoleGroup {
			s.Groups = append(s.Groups, clusterGroup(s, b, lines[b.ID], titles))
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
				group.Items = append(group.Items, labelPrimitive(l, labelRuns[l.ID]))
			}
		}
		s.Groups = append(s.Groups, group)
	}
	for _, b := range s.Boxes {
		if b.Role == scene.RoleNode {
			s.Groups = append(s.Groups, boxGroup(b, lines[b.ID], s.Options.Profile))
		}
	}
}

func textRuns(lines []measure.StyledLine) [][]scene.Run {
	runs := make([][]scene.Run, len(lines))
	for i, l := range lines {
		runs[i] = make([]scene.Run, len(l.Runs))
		for j, run := range l.Runs {
			runs[i][j] = scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic}
		}
	}
	return runs
}

func clusterGroup(s *scene.Scene, b scene.Box, lines [][]scene.Run, titles []Box) *scene.Group {
	group := boxGroup(b, lines, s.Options.Profile)
	text, ok := group.Items[1].(*scene.Text)
	if ok {
		text.Rect = findBox(titles, b.ID)
	}
	return group
}

func boxGroup(b scene.Box, lines [][]scene.Run, p scene.Profile) *scene.Group {
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
	return &scene.Group{Role: role, Owner: b.ID, Items: []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: style}, Rect: b.Rect}, &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: lines}}}
}

func labelPrimitive(l scene.Label, lines [][]scene.Run) *scene.Text {
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
