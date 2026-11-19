package layout

import (
	"math"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	reqmodel "github.com/gosuda/elegant-mermaid/internal/model/requirement"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func FromRequirement(m *reqmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	direction, _ := scene.ParseDirection(m.Direction)
	in := Input{Kind: "requirement", Profile: profile, Direction: direction, Options: resolveOptions(options)}
	for i := range m.Requirements {
		appendRequirementBox(&in, m.Requirements[i].Name, m.Requirements[i].Rows())
	}
	for i := range m.Elements {
		appendRequirementBox(&in, requirementElementID(m, i), m.Elements[i].Rows())
	}
	requirementRelations(&in, m)
	return in, nil
}

func appendRequirementBox(in *Input, id string, rows []string) {
	text := strings.Join(rows, "\n")
	in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: text})
	in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: "requirementBox", Exclusive: true, Text: text})
}

func requirementElementID(m *reqmodel.Model, index int) string {
	if index < 0 || index >= len(m.Elements) {
		return ""
	}
	name := m.Elements[index].Name
	if m.RequirementIndex(name) < 0 {
		return name
	}
	candidate := "element:" + strconv.Itoa(index)
	for m.RequirementIndex(candidate) >= 0 || m.ElementIndex(candidate) >= 0 {
		candidate += ":"
	}
	return candidate
}

func requirementEndpoint(m *reqmodel.Model, node *reqmodel.NodeRef, name string) string {
	switch {
	case node == nil:
		return name
	case node.Element:
		return requirementElementID(m, node.Index)
	case node.Index < len(m.Requirements):
		return m.Requirements[node.Index].Name
	}
	return name
}

func requirementRelations(in *Input, m *reqmodel.Model) {
	type resolved struct {
		label    string
		from, to string
		contains bool
	}
	var links []resolved
	for i := range m.Relationships {
		r := &m.Relationships[i]
		if r.FromNode == nil || r.ToNode == nil {
			continue
		}
		links = append(links, resolved{
			label:    r.Label,
			from:     requirementEndpoint(m, r.FromNode, r.From.Value),
			to:       requirementEndpoint(m, r.ToNode, r.To.Value),
			contains: r.Kind == "contains",
		})
	}
	ids := allocateRouteIDs(in.Boxes, len(links))
	for i, link := range links {
		id := ids[i]
		markerStart, markerEnd, line := "none", "requirement_arrow", "dashed"
		if link.contains {
			markerStart, markerEnd, line = "requirement_contains", "none", "normal"
		}
		in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: link.label})
		in.Routes = append(in.Routes, Route{ID: id, From: link.from, To: link.to, Orthogonal: true, MarkerStart: markerStart, MarkerEnd: markerEnd, Line: line})
	}
}

func requirementConstant(profile scene.Profile, key string) int32 {
	prefix := "vector."
	if profile == scene.ProfileCell {
		prefix = "cell."
	}
	name := prefix + key
	for i := range gen.LayoutConst {
		if gen.LayoutConst[i].Name == name {
			return gen.LayoutConst[i].Value
		}
	}
	return 0
}

func requirementPadding(profile scene.Profile, name string) int32 {
	return requirementConstant(profile, "requirement."+name)
}

func requirementLineHeight(profile scene.Profile) int32 {
	return requirementConstant(profile, "line_h")
}

func requirementMetric(profile scene.Profile) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.ForRole(measure.RoleLabel)
}

func requirementPieceLines(piece string, profile scene.Profile) ([]measure.StyledLine, error) {
	return measure.StyledLines(piece, math.MaxInt32, requirementMetric(profile))
}

func requirementRunLines(piece string, profile scene.Profile) ([][]scene.Run, error) {
	lines, err := requirementPieceLines(piece, profile)
	if err != nil {
		return nil, err
	}
	if len(lines) == 0 {
		lines = []measure.StyledLine{{Runs: []measure.StyledRun{{Text: ""}}}}
	}
	out := make([][]scene.Run, len(lines))
	for i, line := range lines {
		out[i] = make([]scene.Run, len(line.Runs))
		for j, run := range line.Runs {
			out[i][j] = scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic}
		}
	}
	return out, nil
}

func requirementTableSize(text string, profile scene.Profile) (geom.Size, error) {
	paddingX, paddingY := requirementPadding(profile, "padding_x"), requirementPadding(profile, "padding_y")
	lineHeight := int64(requirementLineHeight(profile))
	var width, rows int64
	for piece := range strings.SplitSeq(text, "\n") {
		lines, err := requirementPieceLines(piece, profile)
		if err != nil {
			return geom.Size{}, err
		}
		rows += int64(max(1, len(lines)))
		for _, line := range lines {
			width = max(width, int64(line.Width))
		}
	}
	width += int64(paddingX)
	height := rows*lineHeight + int64(paddingY)
	if width > math.MaxInt32 || height > math.MaxInt32 {
		return geom.Size{}, geom.ErrOverflow
	}
	return geom.Size{W: int32(width), H: int32(height)}, nil
}

func layoutRequirement(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input, err := requirementFamilyInput(in)
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
	err = requirementTableScene(&s, in)
	if err != nil {
		return s, ds, err
	}
	diag.Sort(ds)
	return s, ds, nil
}

func requirementFamilyInput(in Input) (layered.Input, error) {
	input := familyInput(in)
	input.Sizes = make([]geom.Size, len(in.Boxes))
	for i := range in.Boxes {
		size, err := requirementTableSize(in.Boxes[i].Text, in.Profile)
		if err != nil {
			return layered.Input{}, err
		}
		input.Sizes[i] = size
	}
	return input, nil
}

func requirementTableScene(s *scene.Scene, in Input) error {
	for g := range s.Groups {
		if s.Groups[g].Role != scene.GroupRoleNode {
			continue
		}
		id := s.Groups[g].Owner
		text, found := requirementBoxText(in, id)
		if !found {
			continue
		}
		rect, ok := requirementBoxRect(s, id)
		if !ok {
			continue
		}
		items, err := requirementTableItems(text, rect, in.Profile)
		if err != nil {
			return err
		}
		s.Groups[g].Items = items
	}
	return nil
}

func requirementBoxText(in Input, id string) (string, bool) {
	for i := range in.Boxes {
		if in.Boxes[i].ID == id {
			return in.Boxes[i].Text, true
		}
	}
	return "", false
}

func requirementBoxRect(s *scene.Scene, id string) (geom.Rect, bool) {
	for i := range s.Boxes {
		if s.Boxes[i].ID == id {
			return s.Boxes[i].Rect, true
		}
	}
	return geom.Rect{}, false
}

func requirementRows(text string, profile scene.Profile) ([][][]scene.Run, error) {
	pieces := strings.Split(text, "\n")
	rows := make([][][]scene.Run, len(pieces))
	for i, piece := range pieces {
		lines, err := requirementRunLines(piece, profile)
		if err != nil {
			return nil, err
		}
		rows[i] = lines
	}
	return rows, nil
}

func requirementHeaderGap(profile scene.Profile, rowCount int, paddingY int32) int32 {
	if profile == scene.ProfileVector && rowCount > 2 {
		return paddingY / 2
	}
	return 0
}

func requirementHeaderLines(rows [][][]scene.Run) int64 {
	lines := int64(len(rows[0]))
	if len(rows) > 1 {
		lines += int64(len(rows[1]))
	}
	return lines
}

func requirementDivider(rect geom.Rect, y int64) (scene.Primitive, error) {
	line, err := coordinate32(y)
	if err != nil {
		return nil, err
	}
	return &scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{{X: rect.X, Y: line}, {X: rect.X + rect.W, Y: line}}, Corner: 0}, nil
}

func requirementRowRect(x, y, w, h int64) (geom.Rect, error) {
	var out geom.Rect
	for _, field := range []struct {
		dst   *int32
		value int64
	}{{&out.X, x}, {&out.Y, y}, {&out.W, w}, {&out.H, h}} {
		v, err := coordinate32(field.value)
		if err != nil {
			return geom.Rect{}, err
		}
		*field.dst = v
	}
	return out, nil
}

func requirementTableItems(text string, rect geom.Rect, profile scene.Profile) ([]scene.Primitive, error) {
	paddingX, paddingY := requirementPadding(profile, "padding_x"), requirementPadding(profile, "padding_y")
	rows, err := requirementRows(text, profile)
	if err != nil {
		return nil, err
	}
	gap := requirementHeaderGap(profile, len(rows), paddingY)
	height := int64(requirementLineHeight(profile))
	x := int64(rect.X) + int64(paddingX)/2
	top := int64(rect.Y) + int64(paddingY-gap)/2
	width := int64(rect.W) - int64(paddingX)
	divider := int64(top) + requirementHeaderLines(rows)*height + int64(gap)/2
	items := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: rect}}
	if gap > 0 {
		rule, err := requirementDivider(rect, divider)
		if err != nil {
			return nil, err
		}
		items = append(items, rule)
	}
	y := top
	for i, lines := range rows {
		if i == 2 {
			y += int64(gap)
		}
		span := int64(len(lines)) * height
		textRect, err := requirementRowRect(x, y, width, span)
		if err != nil {
			return nil, err
		}
		items = append(items, &scene.Text{Rect: textRect, Role: scene.TextRoleLabel, Size: 14, Align: requirementRowAlign(i), Style: "text", Lines: lines})
		y += span
	}
	return items, nil
}

func coordinate32(v int64) (int32, error) {
	if v < math.MinInt32 || v > math.MaxInt32 {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}

func requirementRowAlign(index int) scene.Align {
	if index < 2 {
		return scene.AlignMiddle
	}
	return scene.AlignStart
}
