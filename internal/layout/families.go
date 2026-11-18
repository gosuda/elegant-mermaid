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

var Families = []Family{{Kind: "flowchart", Layout: layoutFlowchart}, {Kind: "class", Layout: layoutClass}, {Kind: "c4", Layout: layoutC4}, {Kind: "state", Layout: layoutState}, {Kind: "requirement", Layout: layoutRequirement}, {Kind: "er", Layout: layoutER}, {Kind: "usecase", Layout: layoutUsecase}, {Kind: "agentflow", Layout: layoutAgentflow}, {Kind: "swimlane", Layout: layoutSwimlane}, {Kind: "sequence", Layout: layoutSequence}, {Kind: "mindmap", Layout: layoutMindmap}, {Kind: "gitgraph", Layout: layoutGitgraph}, {Kind: "eventmodeling", Layout: layoutEventmodeling}, {Kind: "railroad", Layout: layoutRailroad}, {Kind: "block", Layout: layoutBlock}, {Kind: "xychart", Layout: layoutXYChart}, {Kind: "timeline", Layout: layoutTimeline}, {Kind: "gantt", Layout: layoutGantt}, {Kind: "radar", Layout: layoutRadar}, {Kind: "cynefin", Layout: layoutCynefin}, {Kind: "info", Layout: layoutInfo}, {Kind: "packet", Layout: layoutPacket}, {Kind: "kanban", Layout: layoutKanban}, {Kind: "ishikawa", Layout: layoutIshikawa}, {Kind: "quadrant", Layout: layoutQuadrant}, {Kind: "treemap", Layout: layoutTreemap}, {Kind: "wardley", Layout: layoutWardley},
	{Kind: "journey", Layout: layoutJourney}, {Kind: "pie", Layout: layoutPie},
	{Kind: "venn", Layout: layoutVennChart},
	{Kind: "architecture", Layout: layoutArchitecture},
	{Kind: "treeview", Layout: layoutTreeview},
	{Kind: "sankey", Layout: layoutSankey},
}

func Layout(in Input) (scene.Scene, []diag.Diagnostic, error) {
	for _, f := range Families {
		if f.Kind == in.Kind {
			s, ds, err := f.Layout(in)
			if err == nil && in.Profile == scene.ProfileCell {
				scene.ProjectCellAttachments(&s)
			}
			return s, ds, err
		}
	}
	return scene.Scene{}, nil, fmt.Errorf("unsupported layout kind %q", in.Kind)
}

func layoutFlowchart(in Input) (scene.Scene, []diag.Diagnostic, error) {
	s, budget, ignored, err := layoutLayered(in)
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

func layoutLayered(in Input) (s scene.Scene, budget bool, ignored []string, err error) {
	options := resolveOptions(in.Options)
	options.Profile = in.Profile
	options.Direction = in.Direction
	s, err = layered.LayoutFamily(familyInput(in), layered.Options{Scene: options, BudgetExhausted: &budget, IgnoredDirections: &ignored})
	return s, budget, ignored, err
}

func familyInput(in Input) layered.Input {
	input := layered.Input{Kind: in.Kind}
	for _, b := range in.Boxes {
		input.Boxes = append(input.Boxes, scene.Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive, Direction: b.Direction})
		input.Text = append(input.Text, boxText(in, b))
	}
	for _, r := range in.Routes {
		input.Routes = append(input.Routes, scene.Route{ID: r.ID, From: r.From, To: r.To, Orthogonal: true, MarkerStart: sceneMarker(r.MarkerStart), MarkerEnd: r.MarkerEnd, Stroke: r.Line})
		input.Edges = append(input.Edges, layered.EdgeOptions{MarkerStart: sceneMarker(r.MarkerStart), MarkerEnd: sceneMarker(r.MarkerEnd), Stroke: r.Line, MinLength: edgeMinLength(in.Kind, r), FromSide: r.FromSide, ToSide: r.ToSide})
	}
	for _, l := range in.Labels {
		if routeOwner(in, l.Owner) || groupOwner(in, l.Owner) {
			input.Labels = append(input.Labels, scene.Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
		}
	}
	input.Sizes, input.Exact, input.Attachments, input.RegionSets = in.Sizes, in.Exact, in.Attachments, in.RegionSets
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

func edgeMinLength(kind string, r Route) int32 {
	if kind == "flowchart" {
		return 1
	}
	return int32(max(r.MinLength, 1))
}

func sceneMarker(marker string) string {
	if marker == "none" {
		return ""
	}
	return marker
}
