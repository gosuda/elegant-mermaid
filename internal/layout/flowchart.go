package layout

import (
	"cmp"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func FromFlowchart(m *flowchart.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	direction, _ := scene.ParseDirection(m.Direction)
	in := Input{Kind: "flowchart", Profile: profile, Direction: direction, Options: options}
	for _, n := range m.Nodes {
		if isGroup(m, n.ID) {
			continue
		}
		in.Boxes = append(in.Boxes, Box{ID: n.ID, Role: scene.RoleNode, Shape: n.Shape, Parent: nodeParent(m, n.ID), Exclusive: true, Text: nodeText(n)})
	}
	for _, g := range m.Groups {
		in.Boxes = append(in.Boxes, Box{ID: g.ID, Role: scene.RoleGroup, Parent: g.Parent, Text: g.Title, Direction: g.Direction})
		in.Groups = append(in.Groups, Group{ID: g.ID, DirectionSpan: g.DirSpan})
	}
	slices.SortStableFunc(in.Boxes, func(a, b Box) int {
		return cmp.Compare(boxDeclaration(m, a.ID), boxDeclaration(m, b.ID))
	})
	in.Labels = boxLabels(in.Boxes)
	routeIDs := allocateRouteIDs(in.Boxes, len(m.Edges))
	for i, e := range m.Edges {
		id := routeIDs[i]
		length := 1
		if e.LabelOK {
			length = 2
		}
		in.Routes = append(in.Routes, Route{ID: id, From: e.From, To: e.To, Orthogonal: true, MarkerStart: e.Start, MarkerEnd: e.Marker, Line: e.Stroke, MinLength: length})
		if e.LabelOK {
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: e.Label})
		}
	}
	return in, nil
}

func boxLabels(boxes []Box) []Label {
	var labels []Label
	for _, b := range boxes {
		if b.Text != b.ID {
			labels = append(labels, Label{ID: b.ID + ".label", Owner: b.ID, Role: scene.TextRoleLabel, Text: b.Text})
		}
	}
	return labels
}

func isGroup(m *flowchart.Model, id string) bool {
	for _, g := range m.Groups {
		if g.ID == id {
			return true
		}
	}
	return false
}

func nodeText(n flowchart.Node) string {
	if _, ok := n.Attrs["label"]; ok {
		return n.Label
	}
	if n.LabelKind == "" {
		return n.ID
	}
	return n.Label
}

func boxDeclaration(m *flowchart.Model, id string) int {
	for _, g := range m.Groups {
		if g.ID == id {
			return g.Span.Start
		}
	}
	for _, n := range m.Nodes {
		if n.ID == id {
			return n.First.Start
		}
	}
	return 0
}

func nodeParent(m *flowchart.Model, id string) string {
	parent := ""
	for _, g := range m.Groups {
		if slices.Contains(g.Members, id) {
			parent = g.ID
		}
	}
	return parent
}

func resolveOptions(o scene.Options) scene.Options {
	if o.Thoroughness == 0 {
		o.Thoroughness = 3
	}
	defaults := scene.DefaultLimits()
	if o.Limits.MaxNodes == 0 {
		o.Limits.MaxNodes = defaults.MaxNodes
	}
	if o.Limits.MaxEdges == 0 {
		o.Limits.MaxEdges = defaults.MaxEdges
	}
	if o.Limits.MaxTextBytes == 0 {
		o.Limits.MaxTextBytes = defaults.MaxTextBytes
	}
	o.Config = slices.Clone(o.Config)
	slices.SortStableFunc(o.Config, func(a, b scene.Config) int { return strings.Compare(a.Key, b.Key) })
	return o
}
