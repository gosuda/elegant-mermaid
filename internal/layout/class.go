package layout

import (
	"math"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	model "github.com/gosuda/elegant-mermaid/internal/model/class"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func FromClass(m *model.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	direction, _ := scene.ParseDirection(m.Direction)
	in := Input{Kind: "class", Profile: profile, Direction: direction, Options: options}
	for _, c := range m.Classes {
		rows := classRows(c)
		in.Boxes = append(in.Boxes, Box{ID: c.ID, Role: scene.RoleNode, Parent: c.Parent, Exclusive: true, Shape: "classBox", Text: compartmentText(rows)})
		in.ClassRows = append(in.ClassRows, rows)
	}
	for _, n := range m.Notes {
		in.Boxes = append(in.Boxes, Box{ID: n.ID, Role: scene.RoleNode, Parent: n.Parent, Exclusive: true, Shape: "note", Text: n.Text})
		in.ClassRows = append(in.ClassRows, nil)
	}
	for _, n := range m.Namespaces {
		in.Boxes = append(in.Boxes, Box{ID: n.ID, Role: scene.RoleGroup, Parent: n.Parent, Text: n.Label})
		in.ClassRows = append(in.ClassRows, nil)
	}
	in.Labels = boxLabels(in.Boxes)
	classRoutes(&in, m)
	return in, nil
}

func compartmentText(rows [][]string) string {
	parts := make([]string, len(rows))
	for i, compartment := range rows {
		parts[i] = strings.Join(compartment, "\n")
	}
	return strings.Join(parts, "\n\n")
}

func classRoutes(in *Input, m *model.Model) {
	ids := allocateRouteIDs(in.Boxes, len(m.Relations)+len(m.Notes))
	for i, r := range m.Relations {
		id := ids[i]
		in.Routes = append(in.Routes, Route{ID: id, From: r.From, To: r.To, Orthogonal: true, MarkerStart: r.MarkerStart, MarkerEnd: r.MarkerEnd, Line: r.Line})
		if r.Label != "" {
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Text: r.Label})
		}
	}
	for i, n := range m.Notes {
		if classExists(m, n.Target) {
			in.Routes = append(in.Routes, Route{ID: ids[len(m.Relations)+i], From: n.ID, To: n.Target, Orthogonal: true, MarkerEnd: "none", Line: "dashed"})
		}
	}
}

func classExists(m *model.Model, id string) bool {
	for _, c := range m.Classes {
		if c.ID == id {
			return true
		}
	}
	return false
}

func classRows(c model.Class) [][]string {
	name := c.Label
	if c.Generic != "" {
		name += "<" + c.Generic + ">"
	}
	head := make([]string, 0, len(c.Annotations)+1)
	for _, a := range c.Annotations {
		head = append(head, "«"+a+"»")
	}
	head = append(head, strings.Split(name, "\n")...)
	rows := [][]string{head, {}, {}}
	for _, a := range c.Attributes {
		rows[1] = append(rows[1], a.Text)
	}
	for _, m := range c.Methods {
		rows[2] = append(rows[2], m.Text)
	}
	return rows
}

func classConstant(profile scene.Profile, name string) int32 {
	prefix := "vector."
	if profile == scene.ProfileCell {
		prefix = "cell."
	}
	for _, c := range gen.LayoutConst {
		if c.Name == prefix+name {
			return c.Value
		}
	}
	return 0
}

func ClassSize(rows [][]string, profile scene.Profile) (geom.Size, error) {
	metric := measure.ForRole(measure.RoleLabel)
	if profile == scene.ProfileCell {
		metric = measure.CellMetric()
	}
	var width, height int64
	for _, compartment := range rows {
		height += int64(max(1, len(compartment))) * int64(classConstant(profile, "line_h"))
		w, err := compartmentWidth(compartment, metric)
		if err != nil {
			return geom.Size{}, err
		}
		width = max(width, int64(w))
	}
	width += 2 * int64(classConstant(profile, "class.padding"))
	height += int64(max(0, len(rows)-1)) * int64(classConstant(profile, "class.separator"))
	if profile == scene.ProfileCell {
		height += 2
	}
	if width > math.MaxInt32 || height > math.MaxInt32 {
		return geom.Size{}, geom.ErrOverflow
	}
	return geom.Size{W: int32(width), H: int32(height)}, nil
}

func compartmentWidth(rows []string, metric measure.Metric) (int32, error) {
	var width int32
	for _, row := range rows {
		w, err := metric.TextWidth(row)
		if err != nil {
			return 0, err
		}
		width = max(width, w)
	}
	return width, nil
}

func layoutClass(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input, err := classFamilyInput(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	options := resolveOptions(in.Options)
	options.Profile, options.Direction = in.Profile, in.Direction
	s, err := layered.LayoutFamily(input, layered.Options{Scene: options})
	if err != nil {
		return s, nil, err
	}
	for i, rows := range in.ClassRows {
		if len(rows) > 0 {
			replaceClassGroup(&s, in.Boxes[i].ID, rows)
		}
	}
	for _, b := range in.Boxes {
		if b.Shape == "note" {
			noteStyle(&s, b.ID)
		}
	}
	return s, nil, nil
}
func classFamilyInput(in Input) (layered.Input, error) {
	input := familyInput(in)
	input.Sizes = make([]geom.Size, len(in.Boxes))
	for i, rows := range in.ClassRows {
		if len(rows) == 0 {
			continue
		}
		size, err := ClassSize(rows, in.Profile)
		if err != nil {
			return layered.Input{}, err
		}
		input.Sizes[i] = size
	}
	return input, nil
}

func noteStyle(s *scene.Scene, id string) {
	for _, group := range s.Groups {
		if group.Owner != id {
			continue
		}
		for _, item := range group.Items {
			if rect, ok := item.(*scene.Rect); ok {
				rect.Style = "note"
			}
		}
	}
}

func replaceClassGroup(s *scene.Scene, id string, rows [][]string) {
	var rect geom.Rect
	for _, b := range s.Boxes {
		if b.ID == id {
			rect = b.Rect
			break
		}
	}
	for _, group := range s.Groups {
		if group.Owner == id {
			group.Items = classPrimitives(rect, rows, s.Options.Profile)
		}
	}
}

func classPrimitives(rect geom.Rect, rows [][]string, profile scene.Profile) []scene.Primitive {
	items := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: rect}}
	y := rect.Y
	right := rect.X + rect.W
	if profile == scene.ProfileCell {
		y++
		right--
	}
	var texts []scene.Primitive
	for i, compartment := range rows {
		if i > 0 {
			items = append(items, &scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{{X: rect.X, Y: y}, {X: right, Y: y}}})
			y += classConstant(profile, "class.separator")
		}
		height := int32(max(1, len(compartment))) * classConstant(profile, "line_h")
		textRect := geom.Rect{X: rect.X + classConstant(profile, "class.padding"), Y: y, W: rect.W - 2*classConstant(profile, "class.padding"), H: height}
		texts = append(texts, compartmentPrimitive(textRect, compartment))
		y += height
	}
	return append(items, texts...)
}

func compartmentPrimitive(rect geom.Rect, rows []string) *scene.Text {
	lines := make([][]scene.Run, len(rows))
	for i, text := range rows {
		lines[i] = []scene.Run{{Text: text}}
	}
	return &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignStart, Style: "text", Lines: lines}
}
