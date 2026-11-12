package layout

import (
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type Family struct {
	Kind   string
	Layout func(Input) (scene.Scene, []diag.Diagnostic, error)
}

var Families = []Family{{Kind: "flowchart", Layout: layoutFlowchart}, {Kind: "class", Layout: layoutClass}}

func Layout(in Input) (scene.Scene, []diag.Diagnostic, error) {
	for _, f := range Families {
		if f.Kind == in.Kind {
			return f.Layout(in)
		}
	}
	return scene.Scene{}, nil, fmt.Errorf("unsupported layout kind %q", in.Kind)
}
func layoutFlowchart(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input := familyInput(in)
	options := resolveOptions(in.Options)
	options.Profile = in.Profile
	options.Direction = in.Direction
	var budget bool
	var ignored []string
	s, err := layered.LayoutFamily(input, layered.Options{Scene: options, BudgetExhausted: &budget, IgnoredDirections: &ignored})
	var ds []diag.Diagnostic
	if budget {
		ds = append(ds, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	for _, id := range ignored {
		for _, g := range in.Groups {
			if g.ID == id {
				ds = append(ds, diag.Diagnostic{Code: "flowchart/subgraph-direction-ignored", Severity: diag.SeverityWarning, Message: "subgraph direction is ignored because an edge crosses its boundary", Span: g.DirectionSpan})
			}
		}
	}
	diag.Sort(ds)
	return s, ds, err
}
func familyInput(in Input) layered.Input {
	input := layered.Input{Kind: in.Kind}
	for _, b := range in.Boxes {
		input.Boxes = append(input.Boxes, scene.Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive, Direction: b.Direction})
		input.Text = append(input.Text, boxText(in, b))
	}
	for _, r := range in.Routes {
		input.Routes = append(input.Routes, scene.Route{ID: r.ID, From: r.From, To: r.To, Orthogonal: true, MarkerStart: sceneMarker(r.MarkerStart), MarkerEnd: r.MarkerEnd, Stroke: r.Line})
		input.Edges = append(input.Edges, layered.EdgeOptions{MarkerStart: sceneMarker(r.MarkerStart), MarkerEnd: sceneMarker(r.MarkerEnd), Stroke: r.Line, MinLength: 1})
	}
	for _, l := range in.Labels {
		if routeOwner(in, l.Owner) || groupOwner(in, l.Owner) {
			input.Labels = append(input.Labels, scene.Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
		}
	}
	return input
}
func boxText(in Input, b Box) string {
	for _, l := range in.Labels {
		if l.Owner == b.ID {
			return l.Text
		}
	}
	if b.Text != "" {
		return b.Text
	}
	return b.ID
}
func routeOwner(in Input, id string) bool {
	for _, r := range in.Routes {
		if r.ID == id {
			return true
		}
	}
	return false
}
func groupOwner(in Input, id string) bool {
	for _, b := range in.Boxes {
		if b.ID == id {
			return b.Role == scene.RoleGroup
		}
	}
	return false
}
func sceneMarker(marker string) string {
	if marker == "none" {
		return ""
	}
	return marker
}
