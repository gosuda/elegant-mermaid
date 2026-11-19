package layout

import (
	"context"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	sankeymodel "github.com/gosuda/elegant-mermaid/internal/model/sankey"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	sankeyparser "github.com/gosuda/elegant-mermaid/internal/syntax/sankey"
)

const sankeyKind = "sankey"

func (d *Diagram) resolveSankey() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := sankeyparser.Parse(d.Source, d.Preprocessing.Removed)
	d.sankey, resolved = sankeymodel.Resolve(d.Source, ast)
	return parsed, resolved
}

func (d *Diagram) sankeyInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromSankey(d.sankey, profile, options)
}

func FromSankey(m *sankeymodel.Model, _ scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Config = sankeyConfig(m)
	options.Profile = scene.ProfileVector
	chart := sankeyPayload(m)
	skeleton, err := chartlayout.ModelSkeleton(chart)
	if err != nil {
		return Input{}, nil, err
	}
	in := Input{Kind: sankeyKind, Profile: scene.ProfileVector, Direction: scene.DirectionTB, Options: options, RegionSets: sankeyRegions(chart.Sankey)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	for i, l := range chart.Sankey.Links {
		in.Routes = append(in.Routes, Route{ID: chartlayout.SankeyLinkID(i), From: chartlayout.SankeyNodeID(l.Source), To: chartlayout.SankeyNodeID(l.Target)})
	}
	return in, nil, nil
}

func sankeyConfig(m *sankeymodel.Model) []scene.Config {
	out := make([]scene.Config, 0, len(m.Config))
	for _, e := range m.Config {
		switch e.Value.Kind {
		case sankeymodel.DumpBool:
			out = append(out, scene.ConfigBool(e.Key, e.Value.Bool))
		case sankeymodel.DumpInteger:
			out = append(out, scene.ConfigInt(e.Key, int32(e.Value.Integer)))
		default:
			out = append(out, scene.ConfigString(e.Key, e.Value.String))
		}
	}
	return out
}

func sankeyPayload(m *sankeymodel.Model) *chartmodel.Chart {
	chart := &chartmodel.Chart{Kind: chartmodel.KindSankey}
	for _, e := range m.Config {
		chart.Config = append(chart.Config, sankeyConfigEntry(e))
	}
	s := &chartmodel.Sankey{}
	for _, n := range m.Nodes {
		s.Nodes = append(s.Nodes, chartmodel.SankeyNode{ID: n.ID})
	}
	for _, l := range m.Links {
		kind, value := sankeyValue(l.Value)
		s.Links = append(s.Links, chartmodel.SankeyLink{Source: l.Source, Target: l.Target, Kind: kind, Value: value})
	}
	chart.Sankey = s
	for i, label := range chartlayout.SankeyLabels(chart) {
		s.Nodes[i].Label = label
	}
	return chart
}

func sankeyConfigEntry(e sankeymodel.ConfigEntry) chartmodel.ConfigEntry {
	switch e.Value.Kind {
	case sankeymodel.DumpBool:
		return chartmodel.ConfigEntry{Key: e.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpBool, Bool: e.Value.Bool}}
	case sankeymodel.DumpInteger:
		return chartmodel.ConfigEntry{Key: e.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: e.Value.Integer}}
	}
	return chartmodel.ConfigEntry{Key: e.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpString, String: e.Value.String}}
}

func sankeyValue(v sankeymodel.Value) (chartmodel.ValueKind, chartmodel.Number) {
	switch v.Kind {
	case sankeymodel.ValueNonFinite:
		return chartmodel.ValueNonFinite, 0
	case sankeymodel.ValueOverflow:
		return chartmodel.ValueOverflow, 0
	}
	return chartmodel.ValueFinite, chartmodel.Number(v.Thousandths)
}

func sankeyRegions(s *chartmodel.Sankey) []layered.RegionSet {
	regions := make([]int, 0, 2*len(s.Links))
	for _, l := range s.Links {
		regions = append(regions, int(l.Kind), zigzag(int64(l.Value)))
	}
	return []layered.RegionSet{{Regions: regions}}
}

func sankeyFromInput(in Input) *chartmodel.Chart {
	s := &chartmodel.Sankey{}
	chart := &chartmodel.Chart{Kind: chartmodel.KindSankey, Sankey: s}
	for _, entry := range in.Options.Config {
		chart.Config = append(chart.Config, xychartConfigEntry(entry))
	}
	index := make(map[string]int, len(in.Boxes))
	for i, b := range in.Boxes {
		index[b.ID] = i
		s.Nodes = append(s.Nodes, chartmodel.SankeyNode{})
	}
	for _, l := range in.Labels {
		if at, ok := index[l.Owner]; ok {
			s.Nodes[at].Label = l.Text
		}
	}
	var regions []int
	if len(in.RegionSets) > 0 {
		regions = in.RegionSets[0].Regions
	}
	for i, r := range in.Routes {
		link := chartmodel.SankeyLink{Source: index[r.From], Target: index[r.To]}
		if 2*i+1 < len(regions) {
			link.Kind, link.Value = chartmodel.ValueKind(regions[2*i]), chartmodel.Number(unzigzag(regions[2*i+1]))
		}
		s.Links = append(s.Links, link)
	}
	return chart
}

func layoutSankey(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = scene.ProfileVector
	return chartlayout.Layout(context.Background(), sankeyFromInput(in), options)
}
