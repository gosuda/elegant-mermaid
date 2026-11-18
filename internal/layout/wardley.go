package layout

import (
	"context"
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	wardleymodel "github.com/gosuda/elegant-mermaid/internal/model/wardley"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	wardleyparser "github.com/gosuda/elegant-mermaid/internal/syntax/wardley"
)

const wardleyKind = "wardley"

var defaultWardleyStages = []string{"Genesis", "Custom Built", "Product", "Commodity"}

func (d *Diagram) resolveWardley() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := wardleyparser.Parse(d.Source, d.Preprocessing.Removed)
	d.wardley, resolved = wardleymodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.wardley.AccTitle, d.wardley.AccDescr
	return parsed, resolved
}

func (d *Diagram) wardleyInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromWardley(d.wardley, profile, options)
}

func FromWardley(m *wardleymodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Config = wardleyConfig(m)
	options.Profile = profile
	w := wardleyPayload(m)
	skeleton := w.Skeleton()
	in := Input{Kind: wardleyKind, Profile: profile, Direction: scene.DirectionTB, Options: options, RegionSets: wardleyRegions(w)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, r := range skeleton.Routes {
		in.Routes = append(in.Routes, Route{ID: r.ID, From: r.From, To: r.To, MarkerStart: r.MarkerStart, MarkerEnd: r.MarkerEnd, Line: r.Stroke})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func wardleyConfig(m *wardleymodel.Model) []scene.Config {
	out := make([]scene.Config, 0, len(m.Config))
	for _, entry := range m.Config {
		out = append(out, scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)})
	}
	return out
}

func wardleyPayload(m *wardleymodel.Model) *chartlayout.Wardley {
	w := &chartlayout.Wardley{Title: m.Title, Stages: slices.Clone(m.Stages), Boundaries: slices.Clone(m.Boundaries)}
	if len(w.Stages) == 0 {
		w.Stages = slices.Clone(defaultWardleyStages)
	}
	for _, n := range m.Nodes {
		w.Nodes = append(w.Nodes, wardleyNode(n))
	}
	w.Pipelines = wardleyPipelines(m)
	w.Links = wardleyLinks(m, w.Pipelines)
	for _, t := range m.Trends {
		if i := m.NodeIndex(t.Node); i >= 0 {
			w.Trends = append(w.Trends, chartlayout.WardleyTrend{Node: i, TargetX: t.TargetX, TargetY: t.TargetY})
		}
	}
	for _, n := range m.Notes {
		w.Notes = append(w.Notes, chartlayout.WardleyNote{Text: n.Text, X: n.X, Y: n.Y})
	}
	for _, f := range m.Accelerators {
		w.Accelerators = append(w.Accelerators, chartlayout.WardleyForce{Name: f.Name, X: f.X, Y: f.Y})
	}
	for _, f := range m.Deaccelerators {
		w.Deaccelerators = append(w.Deaccelerators, chartlayout.WardleyForce{Name: f.Name, X: f.X, Y: f.Y})
	}
	for _, a := range m.Annotations {
		w.Annotations = append(w.Annotations, chartlayout.WardleyAnnotation{Number: a.Number, X: a.X, Y: a.Y, Text: a.Text})
	}
	if m.Box != nil {
		w.Box = &chartlayout.WardleyPoint{X: m.Box.X, Y: m.Box.Y}
	}
	return w
}

func wardleyNode(n wardleymodel.Node) chartlayout.WardleyNode {
	return chartlayout.WardleyNode{
		Label: n.Label, X: n.X, Y: n.Y, Anchor: n.Anchor, Inertia: n.Inertia, PipelineParent: n.PipelineParent,
		HasOffset: n.HasOffset, OffsetX: n.OffsetX, OffsetY: n.OffsetY, Strategy: chartlayout.WardleyStrategy(n.Strategy),
	}
}

func wardleyPipelines(m *wardleymodel.Model) []chartlayout.WardleyPipeline {
	var out []chartlayout.WardleyPipeline
	for _, p := range m.Pipelines {
		parent := m.NodeIndex(p.Node)
		var children []int
		for _, id := range p.Components {
			if i := m.NodeIndex(id); i >= 0 {
				children = append(children, i)
			}
		}
		if parent >= 0 && len(children) > 0 {
			out = append(out, chartlayout.WardleyPipeline{Parent: parent, Children: children})
		}
	}
	return out
}

func wardleyLinks(m *wardleymodel.Model, pipelines []chartlayout.WardleyPipeline) []chartlayout.WardleyLink {
	var out []chartlayout.WardleyLink
	for _, l := range m.Links {
		from, to := m.NodeIndex(l.Source), m.NodeIndex(l.Target)
		if from < 0 || to < 0 || joinsPipelineParent(pipelines, from, to) {
			continue
		}
		out = append(out, chartlayout.WardleyLink{From: from, To: to, Dashed: l.Dashed, Label: l.Label, Flow: chartlayout.WardleyFlow(l.Flow)})
	}
	return out
}

func joinsPipelineParent(pipelines []chartlayout.WardleyPipeline, a, b int) bool {
	for _, p := range pipelines {
		if (a == p.Parent && slices.Contains(p.Children, b)) || (b == p.Parent && slices.Contains(p.Children, a)) {
			return true
		}
	}
	return false
}

func wardleyRegions(w *chartlayout.Wardley) []layered.RegionSet {
	sets := w.Regions()
	out := make([]layered.RegionSet, len(sets))
	for i, set := range sets {
		out[i] = layered.RegionSet{Regions: set}
	}
	return out
}

func wardleyFromInput(in Input) (*chartlayout.Wardley, error) {
	var dump chartlayout.WardleyDump
	for _, r := range in.Routes {
		dump.Routes = append(dump.Routes, scene.Route{ID: r.ID, From: r.From, To: r.To, MarkerStart: r.MarkerStart, MarkerEnd: r.MarkerEnd, Stroke: r.Line})
	}
	for _, l := range in.Labels {
		dump.Labels = append(dump.Labels, scene.Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	for _, set := range in.RegionSets {
		dump.Regions = append(dump.Regions, set.Regions)
	}
	return chartlayout.DecodeWardley(dump)
}

func layoutWardley(in Input) (scene.Scene, []diag.Diagnostic, error) {
	w, err := wardleyFromInput(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	options := in.Options
	options.Profile = in.Profile
	return chartlayout.LayoutWardley(context.Background(), w, options)
}
