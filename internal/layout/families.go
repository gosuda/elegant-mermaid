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

var Families = []Family{{Kind: "flowchart", Layout: layoutFlowchart}}

func Layout(in Input) (scene.Scene, []diag.Diagnostic, error) {
	for _, f := range Families {
		if f.Kind == in.Kind {
			return f.Layout(in)
		}
	}
	return scene.Scene{}, nil, fmt.Errorf("unsupported layout kind %q", in.Kind)
}
func layoutFlowchart(in Input) (scene.Scene, []diag.Diagnostic, error) {
	input := layered.Input{Kind: in.Kind}
	for _, b := range in.Boxes {
		input.Boxes = append(input.Boxes, scene.Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
		text := b.ID
		for _, l := range in.Labels {
			if l.Owner == b.ID {
				text = l.Text
				break
			}
		}
		input.Text = append(input.Text, text)
	}
	for _, r := range in.Routes {
		input.Routes = append(input.Routes, scene.Route{ID: r.ID, From: r.From, To: r.To, Orthogonal: true})
		input.Markers = append(input.Markers, r.MarkerEnd)
	}
	options := in.Options
	options.Profile = in.Profile
	options.Direction = in.Direction
	var budget bool
	s, err := layered.LayoutFamily(input, layered.Options{Scene: options, BudgetExhausted: &budget})
	var ds []diag.Diagnostic
	if budget {
		ds = append(ds, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	return s, ds, err
}
