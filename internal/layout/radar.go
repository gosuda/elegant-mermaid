package layout

import (
	"context"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	radarmodel "github.com/gosuda/elegant-mermaid/internal/model/radar"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	radarparser "github.com/gosuda/elegant-mermaid/internal/syntax/radar"
)

const (
	radarKind       = "radar"
	radarTagOptions = 0
	radarTagCurve   = 1
	radarOptionsLen = 7
	radarCurveHead  = 2
)

func (d *Diagram) resolveRadar() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := radarparser.Parse(d.Source, d.Preprocessing.Removed)
	d.radar, resolved = radarmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.radar.AccTitle, d.radar.AccDescr
	return parsed, resolved
}

func (d *Diagram) radarInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	return FromRadar(d.radar, profile, options)
}

func FromRadar(m *radarmodel.Model, _ scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Config = radarConfig(m)
	options.Profile = scene.ProfileVector
	chart := radarPayload(m)
	skeleton, err := chartlayout.ModelSkeleton(chart)
	if err != nil {
		return Input{}, nil, err
	}
	in := Input{Kind: radarKind, Profile: scene.ProfileVector, Direction: scene.DirectionTB, Options: options, RegionSets: radarRegions(chart)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func radarConfig(m *radarmodel.Model) []scene.Config {
	out := make([]scene.Config, len(m.Config))
	for i, entry := range m.Config {
		out[i] = scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)}
	}
	return out
}

func radarPayload(m *radarmodel.Model) *chartmodel.Chart {
	o := m.Options
	radar := &chartmodel.Radar{
		ShowLegend: o.ShowLegend, Ticks: chartmodel.Number(o.Ticks), HasMax: o.HasMax,
		Max: chartmodel.Number(o.Max), Min: chartmodel.Number(o.Min), Graticule: chartmodel.Graticule(o.Graticule),
	}
	for _, axis := range m.Axes {
		radar.Axes = append(radar.Axes, axis.Label)
	}
	for _, curve := range m.Curves {
		out := chartmodel.RadarCurve{Label: curve.Label}
		for _, v := range curve.Values {
			out.Values = append(out.Values, chartmodel.Number(v))
		}
		radar.Curves = append(radar.Curves, out)
	}
	chart := &chartmodel.Chart{Kind: chartmodel.KindRadar, Title: m.Title, Radar: radar}
	for _, entry := range m.Config {
		chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: entry.Value}})
	}
	return chart
}

func radarRegions(c *chartmodel.Chart) []layered.RegionSet {
	r := c.Radar
	legend, hasMax := 0, 0
	if r.ShowLegend {
		legend = 1
	}
	if r.HasMax {
		hasMax = 1
	}
	sets := []layered.RegionSet{{Regions: []int{radarTagOptions, int(r.Graticule), legend, int(r.Ticks), hasMax, zigzag(int64(r.Max)), zigzag(int64(r.Min))}}}
	for _, curve := range r.Curves {
		regions := []int{radarTagCurve, len(curve.Values)}
		for _, v := range curve.Values {
			regions = append(regions, zigzag(int64(v)))
		}
		sets = append(sets, layered.RegionSet{Parent: len(sets), Regions: regions})
	}
	return sets
}

func radarFromInput(in Input) *chartmodel.Chart {
	radar := &chartmodel.Radar{}
	chart := &chartmodel.Chart{Kind: chartmodel.KindRadar, Radar: radar}
	for _, entry := range in.Options.Config {
		if n, err := strconv.ParseInt(entry.Value, 10, 64); err == nil {
			chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: n}})
		}
	}
	for _, set := range in.RegionSets {
		decodeRadarRegion(radar, set.Regions)
	}
	for _, l := range in.Labels {
		decodeRadarLabel(chart, l)
	}
	return chart
}

func decodeRadarRegion(radar *chartmodel.Radar, r []int) {
	switch {
	case len(r) >= radarOptionsLen && r[0] == radarTagOptions:
		radar.Graticule = chartmodel.Graticule(r[1])
		radar.ShowLegend = r[2] == 1
		radar.Ticks = chartmodel.Number(r[3])
		radar.HasMax = r[4] == 1
		radar.Max, radar.Min = chartmodel.Number(unzigzag(r[5])), chartmodel.Number(unzigzag(r[6]))
	case len(r) >= radarCurveHead && r[0] == radarTagCurve:
		radar.Curves = append(radar.Curves, decodeRadarCurve(r))
	}
}

func decodeRadarCurve(r []int) chartmodel.RadarCurve {
	var curve chartmodel.RadarCurve
	for at := radarCurveHead; at < len(r) && len(curve.Values) < r[1]; at++ {
		curve.Values = append(curve.Values, chartmodel.Number(unzigzag(r[at])))
	}
	return curve
}

func decodeRadarLabel(chart *chartmodel.Chart, l Label) {
	radar := chart.Radar
	if rest, ok := strings.CutPrefix(l.ID, "legend."); ok {
		if i, err := strconv.Atoi(rest); err == nil && i >= 0 && i < len(radar.Curves) {
			radar.Curves[i].Label = l.Text
		}
		return
	}
	if _, ok := strings.CutPrefix(l.ID, "axis."); ok {
		radar.Axes = append(radar.Axes, l.Text)
		return
	}
	if l.ID == "title" {
		chart.Title = l.Text
	}
}

func layoutRadar(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = scene.ProfileVector
	return chartlayout.Layout(context.Background(), radarFromInput(in), options)
}
