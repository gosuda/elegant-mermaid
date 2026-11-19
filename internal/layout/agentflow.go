package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	agentflowmodel "github.com/gosuda/elegant-mermaid/internal/model/agentflow"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax"
)

func FromAgentflow(m *agentflowmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	direction, _ := scene.ParseDirection(m.Direction)
	in := Input{
		Kind:      "agentflow",
		Profile:   profile,
		Direction: direction,
		Options:   options,
	}
	for _, declaration := range m.Declarations {
		var err error
		if declaration.IsGroup {
			err = appendAgentflowGroup(&in, m, declaration.Group)
		} else {
			err = appendAgentflowNode(&in, m, declaration.Node)
		}
		if err != nil {
			return Input{}, nil, err
		}
	}
	for _, b := range in.Boxes {
		if b.Text != b.ID {
			in.Labels = append(in.Labels, Label{ID: b.ID + ".label", Owner: b.ID, Text: b.Text})
		}
	}
	if err := appendAgentflowEdges(&in, m); err != nil {
		return Input{}, nil, err
	}
	return in, nil, nil
}

func appendAgentflowNode(in *Input, m *agentflowmodel.Model, index int) error {
	if index >= len(m.Nodes) {
		return nil
	}
	node := &m.Nodes[index]
	text, size, err := agentflowContent(node.Label, m, in.Profile)
	if err != nil {
		return err
	}
	in.Boxes = append(in.Boxes, Box{ID: node.ID, Role: scene.RoleNode, Shape: node.Shape, Parent: node.Parent, Exclusive: true, Text: text})
	in.Sizes = append(in.Sizes, size)
	return nil
}

func agentflowCollapsed(a *agentflowmodel.Appearance) bool {
	for _, entry := range a.Metadata {
		if entry.Key == "view" && entry.Value.Kind == syn.ValueString && entry.Value.Text == "collapsed" {
			return true
		}
	}
	return false
}

func appendAgentflowGroup(in *Input, m *agentflowmodel.Model, index int) error {
	if index >= len(m.Groups) {
		return nil
	}
	group := &m.Groups[index]
	if agentflowHiddenGroup(m, group.Parent) {
		return nil
	}
	collapsed := agentflowCollapsed(&group.Appearance)
	text, size, err := agentflowContent(group.Title, m, in.Profile)
	if err != nil {
		return err
	}
	shape, role, exclusive := "", scene.RoleGroup, false
	if collapsed {
		shape, role, exclusive = "collapsedGroup", scene.RoleNode, true
		_, padY, err := agentflowPadding(m, in.Profile)
		if err != nil {
			return err
		}
		size.H += agentflowLineHeight(in.Profile) + padY
	}
	in.Boxes = append(in.Boxes, Box{ID: group.ID, Role: role, Shape: shape, Parent: group.Parent, Exclusive: exclusive, Direction: group.Direction, Text: text})
	if !collapsed {
		in.Groups = append(in.Groups, Group{ID: group.ID, DirectionSpan: group.DirectionSpan})
	}
	in.Sizes = append(in.Sizes, size)
	return nil
}

func agentflowHiddenGroup(m *agentflowmodel.Model, parent string) bool {
	for {
		index := agentflowGroupIndex(m, parent)
		if index < 0 {
			return false
		}
		if agentflowCollapsed(&m.Groups[index].Appearance) {
			return true
		}
		parent = m.Groups[index].Parent
	}
}

func agentflowGroupIndex(m *agentflowmodel.Model, id string) int {
	for i := range m.Groups {
		if m.Groups[i].ID == id {
			return i
		}
	}
	return -1
}

func agentflowKindConstant(profile scene.Profile, name string) (int32, bool) {
	key := profile.String() + ".agentflow." + name
	for i := range gen.LayoutConst {
		if gen.LayoutConst[i].Name == key {
			return gen.LayoutConst[i].Value, true
		}
	}
	return 0, false
}

func agentflowConstant(profile scene.Profile, name string) (int32, error) {
	value, ok := agentflowKindConstant(profile, name)
	if !ok {
		return 0, geom.ErrDomain
	}
	return value, nil
}

func agentflowMetric(profile scene.Profile) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.ForRole(measure.RoleLabel)
}

func agentflowLineHeight(profile scene.Profile) int32 {
	if profile == scene.ProfileCell {
		return 1
	}
	return measure.RoleLabel.LineHeightPx() * 64
}

func agentflowMeasured(text string, profile scene.Profile) (int32, int32, error) {
	target, err := agentflowConstant(profile, "wrapping_width")
	if err != nil {
		return 0, 0, err
	}
	lines, err := measure.StyledLines(text, target, agentflowMetric(profile))
	if err != nil {
		return 0, 0, err
	}
	width := int32(0)
	for _, line := range lines {
		width = max(width, line.Width)
	}
	height, err := agentflowCheckedI32(int64(len(lines)) * int64(agentflowLineHeight(profile)))
	if err != nil {
		return 0, 0, err
	}
	return width, height, nil
}

func agentflowContent(text string, m *agentflowmodel.Model, profile scene.Profile) (string, geom.Size, error) {
	width, height, err := agentflowMeasured(text, profile)
	if err != nil {
		return "", geom.Size{}, err
	}
	padX, padY, err := agentflowPadding(m, profile)
	if err != nil {
		return "", geom.Size{}, err
	}
	width += 2 * padX
	height += 2 * padY
	minWidth, err := agentflowConstant(profile, "min_node_width")
	if err != nil {
		return "", geom.Size{}, err
	}
	return text, geom.Size{W: max(width, minWidth), H: height}, nil
}

func agentflowPadding(m *agentflowmodel.Model, profile scene.Profile) (int32, int32, error) {
	if !m.PaddingSet {
		padding, err := agentflowConstant(profile, "padding")
		if err != nil {
			return 0, 0, err
		}
		return padding, padding, nil
	}
	padding := int32(m.Padding)
	if padding < 0 {
		return 0, 0, geom.ErrDomain
	}
	if profile == scene.ProfileVector {
		scaled, err := agentflowCheckedI32(int64(padding) * 64)
		if err != nil {
			return 0, 0, err
		}
		return scaled, scaled, nil
	}
	x, err := agentflowCheckedI32(measure.CeilDiv(int64(padding), 8))
	if err != nil {
		return 0, 0, err
	}
	y, err := agentflowCheckedI32(measure.CeilDiv(int64(padding), 16))
	if err != nil {
		return 0, 0, err
	}
	return max(x, 1), max(y, 1), nil
}

func appendAgentflowEdges(in *Input, m *agentflowmodel.Model) error {
	count := countAgentflowEdges(in, m)
	ids := allocateRouteIDs(in.Boxes, count)
	next := 0
	for i := range m.Edges {
		edge := &m.Edges[i]
		if edge.Line == "invisible" || !agentflowBoxExists(in, edge.From) || !agentflowBoxExists(in, edge.To) {
			continue
		}
		id := ids[next]
		next++
		if edge.Label != "" {
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Text: edge.Label})
		}
		in.Routes = append(in.Routes, Route{
			ID: id, From: edge.From, To: edge.To, Orthogonal: true,
			MarkerStart: "none", MarkerEnd: edge.Marker, Line: edge.Line,
			MinLength: max(edge.Length, 1),
		})
	}
	return nil
}

func countAgentflowEdges(in *Input, m *agentflowmodel.Model) int {
	count := 0
	for i := range m.Edges {
		edge := &m.Edges[i]
		if edge.Line != "invisible" && agentflowBoxExists(in, edge.From) && agentflowBoxExists(in, edge.To) {
			count++
		}
	}
	return count
}

func agentflowBoxExists(in *Input, id string) bool {
	for i := range in.Boxes {
		if in.Boxes[i].ID == id {
			return true
		}
	}
	return false
}

func agentflowCheckedI32(v int64) (int32, error) {
	if v < int64(geom.I32Min) || v > int64(geom.I32Max) {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}
