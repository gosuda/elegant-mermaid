package layout

import (
	"context"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	piemodel "github.com/gosuda/elegant-mermaid/internal/model/pie"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	pieparser "github.com/gosuda/elegant-mermaid/internal/syntax/pie"
)

const (
	pieKind       = "pie"
	pieTagMeta    = 0
	pieTagSection = 1
	pieShowData   = 1
)

func (d *Diagram) resolvePie() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := pieparser.Parse(d.Source, d.Preprocessing.Removed)
	d.pie, resolved = piemodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.pie.AccTitle, d.pie.AccDescr
	return parsed, resolved
}

func (d *Diagram) pieInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromPie(d.pie, profile, options)
}

func FromPie(m *piemodel.Model, _ scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Config = pieConfig(m)
	options.Profile = scene.ProfileVector
	chart := piePayload(m)
	skeleton, err := chartlayout.ModelSkeleton(chart)
	if err != nil {
		return Input{}, nil, err
	}
	in := Input{Kind: pieKind, Profile: scene.ProfileVector, Direction: scene.DirectionTB, Options: options, RegionSets: pieRegions(chart)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func pieConfig(m *piemodel.Model) []scene.Config {
	out := make([]scene.Config, len(m.Config))
	for i, entry := range m.Config {
		out[i] = scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)}
	}
	return out
}

func piePayload(m *piemodel.Model) *chartmodel.Chart {
	pie := &chartmodel.Pie{ShowData: m.ShowData}
	for _, s := range m.Sections {
		pie.Sections = append(pie.Sections, chartmodel.PieSection{Label: s.Label, Value: chartmodel.Number(s.Value), Index: s.Index})
	}
	chart := &chartmodel.Chart{Kind: chartmodel.KindPie, Title: m.Title, Pie: pie}
	for _, entry := range m.Config {
		chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: entry.Value}})
	}
	return chart
}

func pieRegions(c *chartmodel.Chart) []layered.RegionSet {
	showData := 0
	if c.Pie.ShowData {
		showData = pieShowData
	}
	sets := []layered.RegionSet{{Regions: []int{pieTagMeta, showData}}}
	for _, s := range c.Pie.Sections {
		sets = append(sets, layered.RegionSet{Parent: len(sets), Regions: []int{pieTagSection, int(s.Value), s.Index}})
	}
	return sets
}

func pieFromInput(in Input) *chartmodel.Chart {
	pie := &chartmodel.Pie{}
	chart := &chartmodel.Chart{Kind: chartmodel.KindPie, Pie: pie}
	for _, entry := range in.Options.Config {
		if n, err := strconv.ParseInt(entry.Value, 10, 64); err == nil {
			chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: n}})
		}
	}
	for _, set := range in.RegionSets {
		decodePieRegion(pie, set.Regions)
	}
	for _, l := range in.Labels {
		decodePieLabel(chart, l)
	}
	return chart
}

func decodePieRegion(pie *chartmodel.Pie, r []int) {
	switch {
	case len(r) >= 2 && r[0] == pieTagMeta:
		pie.ShowData = r[1] == pieShowData
	case len(r) >= 3 && r[0] == pieTagSection:
		pie.Sections = append(pie.Sections, chartmodel.PieSection{Value: chartmodel.Number(r[1]), Index: r[2]})
	}
}

func decodePieLabel(chart *chartmodel.Chart, l Label) {
	if l.ID == "title" {
		chart.Title = l.Text
		return
	}
	rest, ok := strings.CutPrefix(l.ID, "legend.")
	if !ok {
		return
	}
	i, err := strconv.Atoi(rest)
	if err != nil || i < 0 || i >= len(chart.Pie.Sections) {
		return
	}
	s := &chart.Pie.Sections[i]
	s.Label = l.Text
	if chart.Pie.ShowData {
		s.Label = strings.TrimSuffix(l.Text, " ["+chartlayout.FormatNumber(int64(s.Value))+"]")
	}
}

func layoutPie(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = scene.ProfileVector
	return chartlayout.Layout(context.Background(), pieFromInput(in), options)
}
