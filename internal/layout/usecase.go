package layout

import (
	"math"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	model "github.com/gosuda/elegant-mermaid/internal/model/usecase"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func FromUsecase(m *model.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	direction, _ := scene.ParseDirection(m.Direction)
	in := Input{Kind: "usecase", Profile: profile, Direction: direction, Options: resolveOptions(options)}
	usecaseBoxes(&in, m)
	in.Labels = boxLabels(in.Boxes)
	usecaseRoutes(&in, m)
	return in, nil
}

func usecaseBoxes(in *Input, m *model.Model) {
	notes := m.Notes
	for i := range m.Nodes {
		node := &m.Nodes[i]
		for len(notes) > 0 && notes[0].Span.Start < node.FirstSpan.Start {
			usecaseNote(in, m, &notes[0])
			notes = notes[1:]
		}
		usecaseNode(in, node)
	}
	for i := range notes {
		usecaseNote(in, m, &notes[i])
	}
}

func usecaseNote(in *Input, m *model.Model, note *model.Note) {
	var parent string
	for i := range m.Nodes {
		if m.Nodes[i].ID == note.Target {
			parent = m.Nodes[i].Parent
			break
		}
	}
	in.Boxes = append(in.Boxes, Box{ID: note.ID, Role: scene.RoleNode, Shape: "note", Parent: parent, Exclusive: true, Text: note.Text})
}

func usecaseNode(in *Input, node *model.Node) {
	boundary := node.Kind == model.KindBoundary
	role := scene.RoleNode
	if boundary {
		role = scene.RoleGroup
	}
	in.Boxes = append(in.Boxes, Box{ID: node.ID, Role: role, Shape: usecaseShape(node), Parent: node.Parent, Exclusive: !boundary, Text: usecaseDisplay(node)})
}

func usecaseShape(node *model.Node) string {
	switch {
	case node.Kind == model.KindActor:
		return usecaseActorShape(node)
	case node.Kind == model.KindUsecase && node.Business:
		return "usecaseBusiness"
	case node.Kind == model.KindBoundary && node.BoundaryType == "package":
		return "rect:package"
	}
	return node.Shape
}

func usecaseActorShape(node *model.Node) string {
	if node.Icon != "" {
		flag := "icon"
		if node.Business {
			flag = "business"
		}
		return "usecaseActorIcon:" + flag + ":" + node.Icon
	}
	base := "usecaseActor"
	switch node.ActorType {
	case "hollow":
		base = "usecaseActorHollow"
	case "awesome":
		base = "usecaseActorAwesome"
	}
	if node.Business {
		return base + ":business"
	}
	return base
}

func usecaseDisplay(node *model.Node) string {
	label := node.Label
	if node.JSON != nil {
		label = usecaseJSONText(node.JSON)
	}
	if node.Stereotype == "" {
		return label
	}
	return "«" + node.Stereotype + "»<br/>" + label
}

func usecaseJSONText(value *model.JSON) string {
	switch value.Kind {
	case model.JSONObject:
		parts := make([]string, len(value.Keys))
		for i, key := range value.Keys {
			parts[i] = key + ":" + usecaseJSONText(&value.Values[i])
		}
		return "{" + strings.Join(parts, ",") + "}"
	case model.JSONArray:
		parts := make([]string, len(value.Values))
		for i := range value.Values {
			parts[i] = usecaseJSONText(&value.Values[i])
		}
		return "[" + strings.Join(parts, ",") + "]"
	}
	return value.Scalar
}

func usecaseRoutes(in *Input, m *model.Model) {
	ids := allocateRouteIDs(in.Boxes, len(m.Relations)+len(m.Notes))
	for i := range m.Relations {
		edge := &m.Relations[i]
		id := ids[i]
		if edge.Label != "" {
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: edge.Label})
		}
		line := "normal"
		if edge.Kind == "include" || edge.Kind == "extend" {
			line = "dotted"
		}
		in.Routes = append(in.Routes, Route{ID: id, From: edge.From, To: edge.To, Orthogonal: true, MarkerStart: edge.MarkerStart, MarkerEnd: edge.MarkerEnd, Line: line, MinLength: edge.MinLength})
	}
	for i := range m.Notes {
		note := &m.Notes[i]
		in.Routes = append(in.Routes, Route{ID: ids[len(m.Relations)+i], From: note.ID, To: note.Target, Orthogonal: true, MarkerStart: "none", MarkerEnd: "none", Line: "normal", MinLength: 1})
	}
}

func usecaseConstant(profile scene.Profile, name string) int32 {
	key := profile.String() + "." + name
	for i := range gen.LayoutConst {
		if gen.LayoutConst[i].Name == key {
			return gen.LayoutConst[i].Value
		}
	}
	return 0
}

func usecaseMetric(profile scene.Profile) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.ForRole(measure.RoleLabel)
}

func usecaseInt32(v int64) (int32, error) {
	if v < math.MinInt32 || v > math.MaxInt32 {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}

func usecaseFamilyInput(in Input) (layered.Input, error) {
	input := familyInput(in)
	input.Sizes = make([]geom.Size, len(in.Boxes))
	input.Exact = make([]bool, len(in.Boxes))
	for i, b := range in.Boxes {
		size, exact, err := usecaseNodeSize(b, in.Profile)
		if err != nil {
			return layered.Input{}, err
		}
		input.Sizes[i], input.Exact[i] = size, exact
	}
	return input, nil
}

func usecaseNodeSize(b Box, profile scene.Profile) (geom.Size, bool, error) {
	spec := parseUsecaseShape(b.Shape)
	if !spec.isActor() && spec.id != "usecaseEllipse" && spec.id != "usecaseBusiness" {
		return geom.Size{}, false, nil
	}
	lines, err := measure.StyledLines(b.Text, usecaseConstant(profile, "usecase.wrapping_width"), usecaseMetric(profile))
	if err != nil {
		return geom.Size{}, false, err
	}
	var width int32
	for _, line := range lines {
		width = max(width, line.Width)
	}
	height, err := usecaseInt32(int64(max(len(lines), 1)) * int64(usecaseConstant(profile, "line_h")))
	if err != nil {
		return geom.Size{}, false, err
	}
	if spec.isActor() {
		size, err := usecaseActorSize(width, height, profile)
		return size, true, err
	}
	padX := int64(usecaseConstant(profile, "node_pad_x")) + int64(usecaseConstant(profile, "node_border"))
	padY := int64(usecaseConstant(profile, "node_pad_y")) + int64(usecaseConstant(profile, "node_border"))
	w, err := usecaseInt32(int64(width) + 2*padX)
	if err != nil {
		return geom.Size{}, false, err
	}
	h, err := usecaseInt32(int64(height) + 2*padY)
	if err != nil {
		return geom.Size{}, false, err
	}
	return geom.Size{W: max(w, usecaseConstant(profile, "usecase.min_node_width")), H: h}, false, nil
}

func usecaseActorSize(width, height int32, profile scene.Profile) (geom.Size, error) {
	figureW, figureH, padding, gap := int64(56*64), int64(72*64), int64(8*64), int64(8*64)
	if profile == scene.ProfileCell {
		figureW, figureH, padding, gap = 7, 5, 1, 1
	}
	w, err := usecaseInt32(max(int64(width), figureW) + 2*padding)
	if err != nil {
		return geom.Size{}, err
	}
	h, err := usecaseInt32(int64(height) + figureH + gap + 2*padding)
	return geom.Size{W: w, H: h}, err
}

func layoutUsecase(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input, err := usecaseFamilyInput(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	options := resolveOptions(in.Options)
	options.Profile, options.Direction = in.Profile, in.Direction
	var budget bool
	s, err := layered.LayoutFamily(input, layered.Options{Scene: options, BudgetExhausted: &budget})
	var ds []diag.Diagnostic
	if budget {
		ds = append(ds, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	if err != nil {
		return s, ds, err
	}
	return s, ds, usecaseDrawShapes(in, &s)
}
