package layout

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	c4model "github.com/gosuda/elegant-mermaid/internal/model/c4"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func FromC4(m *c4model.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	direction, _ := scene.ParseDirection(m.Direction)
	in := Input{Kind: "c4", Profile: profile, Direction: direction, Options: resolveOptions(options)}
	ids := c4BoundaryIDs(m)
	for _, d := range m.Declarations {
		c4AppendDeclaration(&in, m, d, ids)
	}
	in.Labels = boxLabels(in.Boxes)
	routeIDs := allocateRouteIDs(in.Boxes, len(m.Relations))
	for _, r := range m.Relations {
		from, ok := c4EndpointID(m, ids, r.From.Value)
		if !ok {
			continue
		}
		to, ok := c4EndpointID(m, ids, r.To.Value)
		if !ok {
			continue
		}
		id := routeIDs[len(in.Routes)]
		start, end := c4RelationMarkers(r.MacroName)
		fromSide, toSide := c4RelationSides(r.MacroName)
		in.Routes = append(in.Routes, Route{ID: id, From: from, To: to, Orthogonal: true, MarkerStart: start, MarkerEnd: end, Line: "normal", MinLength: 1, FromSide: fromSide, ToSide: toSide})
		c4AppendRelationLabel(&in, id, c4DisplayText(r.Label.Value, r.Fields))
	}
	return in, nil
}

func c4EndpointID(m *c4model.Model, ids []string, alias string) (string, bool) {
	for _, e := range m.Elements {
		if e.ID == alias {
			return alias, true
		}
	}
	id := c4Parent(m, ids, alias)
	return id, id != ""
}

func c4RelationMarkers(name string) (string, string) {
	start, end := "none", "point"
	if name == "BiRel" || name == "Rel_Back" {
		start = "point"
	}
	if name == "Rel_Back" {
		end = "none"
	}
	return start, end
}

func c4AppendRelationLabel(in *Input, id, text string) {
	if text == "" {
		return
	}
	in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: text})
}

func c4Parent(m *c4model.Model, ids []string, alias string) string {
	for i, b := range m.Boundaries {
		if b.ID == alias {
			return ids[i]
		}
	}
	return ""
}

func c4Shape(kind string) string {
	if kind == "person" || kind == "external_person" {
		return "person"
	}
	if strings.HasSuffix(kind, "_db") {
		return "cyl"
	}
	return "rect"
}

func c4AppendDeclaration(in *Input, m *c4model.Model, d c4model.Declaration, ids []string) {
	switch d.Target {
	case c4model.DeclarationElement:
		if d.Index < 0 || d.Index >= len(m.Elements) {
			return
		}
		e := m.Elements[d.Index]
		in.Boxes = append(in.Boxes, Box{ID: e.ID, Role: scene.RoleNode, Shape: c4Shape(e.Kind), Parent: c4Parent(m, ids, e.Parent), Exclusive: true, Text: c4DisplayText(e.Label.Value, e.Fields)})
	case c4model.DeclarationBoundary:
		if d.Index < 0 || d.Index >= len(m.Boundaries) {
			return
		}
		b := m.Boundaries[d.Index]
		in.Boxes = append(in.Boxes, Box{ID: ids[d.Index], Role: scene.RoleGroup, Parent: c4Parent(m, ids, b.Parent), Text: c4DisplayText(b.Label.Value, b.Fields)})
		in.Groups = append(in.Groups, Group{ID: ids[d.Index], DirectionSpan: b.MacroSpan})
	}
}

func c4BoundaryIDs(m *c4model.Model) []string {
	reserved := make(map[string]bool, len(m.Elements)+len(m.Boundaries))
	for _, e := range m.Elements {
		reserved[e.ID] = true
	}
	for _, b := range m.Boundaries {
		reserved[b.ID] = true
	}
	ids := make([]string, len(m.Boundaries))
	next := 0
	for i, b := range m.Boundaries {
		ids[i] = b.ID
		collision := false
		for _, e := range m.Elements {
			if e.ID == b.ID {
				collision = true
				break
			}
		}
		if !collision {
			continue
		}
		for {
			id := "c4group" + strconv.Itoa(next)
			next++
			if !reserved[id] {
				reserved[id] = true
				ids[i] = id
				break
			}
		}
	}
	return ids
}

func c4DisplayText(label string, fields []c4model.Field) string {
	lines := [4]string{label}
	n := 1
	for _, name := range [...]string{"type", "techn", "descr"} {
		for _, f := range fields {
			if f.Name == name && f.Value.Value != "" {
				lines[n] = f.Value.Value
				n++
				break
			}
		}
	}
	return strings.Join(lines[:n], "<br/>")
}

func c4RelationSides(name string) (geom.Side, geom.Side) {
	switch name {
	case "Rel_Up", "Rel_U":
		return geom.SideTop, geom.SideBottom
	case "Rel_Down", "Rel_D":
		return geom.SideBottom, geom.SideTop
	case "Rel_Left", "Rel_L":
		return geom.SideLeft, geom.SideRight
	case "Rel_Right", "Rel_R":
		return geom.SideRight, geom.SideLeft
	default:
		return geom.SideNone, geom.SideNone
	}
}

func layoutC4(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input := familyInput(in)
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
	s, err = layered.RerouteEndpoints(input, s)
	if err != nil {
		return s, ds, err
	}
	err = c4ShapeScene(in, &s)
	return s, ds, err
}
