package layout

import (
	"context"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	chartlayout "github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	xychartmodel "github.com/gosuda/elegant-mermaid/internal/model/xychart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	xychartKind = "xychart"

	xychartTagAxes = 0
	xychartTagPlot = 1

	xychartPresent  = 1
	xychartHasX     = 2
	xychartPerPoint = 4
)

func FromXYChart(m *xychartmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	options = resolveOptions(options)
	options.Config = xychartConfig(m)
	options.Profile = profile
	chart := xychartPayload(m)
	skeleton, err := chartlayout.ModelSkeleton(chart)
	if err != nil {
		return Input{}, nil, err
	}
	in := Input{Kind: xychartKind, Profile: profile, Direction: scene.DirectionTB, Options: options, RegionSets: xychartRegions(chart)}
	for _, b := range skeleton.Boxes {
		in.Boxes = append(in.Boxes, Box{ID: b.ID, Role: b.Role, Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, l := range skeleton.Labels {
		in.Labels = append(in.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text})
	}
	return in, nil, nil
}

func xychartConfig(m *xychartmodel.Model) []scene.Config {
	var out []scene.Config
	for _, entry := range m.Config {
		if entry.Value.Kind == xychartmodel.DumpBool {
			out = append(out, scene.ConfigBool(entry.Key, entry.Value.Bool))
			continue
		}
		out = append(out, scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value.Integer, 10)})
	}
	if m.Orientation == xychartmodel.Horizontal {
		out = append(out, scene.ConfigString("chartOrientation", m.Orientation.String()))
	}
	slices.SortFunc(out, func(a, b scene.Config) int { return strings.Compare(a.Key, b.Key) })
	return out
}

func xychartPayload(m *xychartmodel.Model) *chartmodel.Chart {
	chart := &chartmodel.Chart{Kind: chartmodel.KindXYChart, Title: m.Title}
	for _, entry := range m.Config {
		value := chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: entry.Value.Integer}
		if entry.Value.Kind == xychartmodel.DumpBool {
			value = chartmodel.DumpValue{Kind: chartmodel.DumpBool, Bool: entry.Value.Bool}
		}
		chart.Config = append(chart.Config, chartmodel.ConfigEntry{Key: entry.Key, Value: value})
	}
	xy := &chartmodel.XY{
		XTitle: m.X.Title, YTitle: m.Y.Title,
		XAxis: chartmodel.XAxis{Band: m.X.Band, Categories: m.X.Categories, Min: chartmodel.Number(m.X.Min), Max: chartmodel.Number(m.X.Max)},
		YAxis: chartmodel.YAxis{Min: chartmodel.Number(m.Y.Min), Max: chartmodel.Number(m.Y.Max)},
	}
	if m.Orientation == xychartmodel.Horizontal {
		xy.Orientation = chartmodel.OrientationHorizontal
	}
	for _, plot := range m.Plots {
		out := chartmodel.Plot{Kind: chartmodel.PlotBar, Title: plot.Title}
		if plot.Line {
			out.Kind = chartmodel.PlotLine
		}
		for _, p := range plot.Points {
			out.Points = append(out.Points, chartmodel.Point{Present: p.Present, Slot: p.Slot, HasX: p.HasX, X: chartmodel.Number(p.X), Value: chartmodel.Number(p.Y), Label: p.Label})
		}
		xy.Plots = append(xy.Plots, out)
	}
	chart.XY = xy
	return chart
}

func zigzag(v int64) int {
	if v < 0 {
		return int(-2*v - 1)
	}
	return int(2 * v)
}

func unzigzag(n int) int64 {
	if n%2 == 1 {
		return -(int64(n) + 1) / 2
	}
	return int64(n) / 2
}

func xychartRegions(c *chartmodel.Chart) []layered.RegionSet {
	xy := c.XY
	horizontal, band := 0, 0
	if xy.Orientation == chartmodel.OrientationHorizontal {
		horizontal = 1
	}
	if xy.XAxis.Band {
		band = 1
	}
	sets := []layered.RegionSet{{Regions: []int{xychartTagAxes, horizontal, band, zigzag(int64(xy.XAxis.Min)), zigzag(int64(xy.XAxis.Max)), zigzag(int64(xy.YAxis.Min)), zigzag(int64(xy.YAxis.Max))}}}
	for _, plot := range xy.Plots {
		regions := []int{xychartTagPlot, int(plot.Kind), len(plot.Points)}
		for _, p := range plot.Points {
			flags := 0
			if p.Present {
				flags |= xychartPresent
			}
			if p.HasX {
				flags |= xychartHasX
			}
			regions = append(regions, flags, p.Slot+1, zigzag(int64(p.X)), zigzag(int64(p.Value)))
		}
		sets = append(sets, layered.RegionSet{Parent: len(sets), Regions: regions})
	}
	return sets
}

func xychartFromInput(in Input) *chartmodel.Chart {
	xy := &chartmodel.XY{}
	chart := &chartmodel.Chart{Kind: chartmodel.KindXYChart, XY: xy}
	for _, entry := range in.Options.Config {
		chart.Config = append(chart.Config, xychartConfigEntry(entry))
	}
	for _, set := range in.RegionSets {
		decodeXYRegion(xy, set.Regions)
	}
	for _, l := range in.Labels {
		decodeXYLabel(chart, l)
	}
	return chart
}

func xychartConfigEntry(entry scene.Config) chartmodel.ConfigEntry {
	if entry.Value == "true" || entry.Value == "false" {
		return chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpBool, Bool: entry.Value == "true"}}
	}
	if n, err := strconv.ParseInt(entry.Value, 10, 64); err == nil {
		return chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: n}}
	}
	text, err := strconv.Unquote(entry.Value)
	if err != nil {
		text = entry.Value
	}
	return chartmodel.ConfigEntry{Key: entry.Key, Value: chartmodel.DumpValue{Kind: chartmodel.DumpString, String: text}}
}

func decodeXYRegion(xy *chartmodel.XY, r []int) {
	switch {
	case len(r) >= 7 && r[0] == xychartTagAxes:
		xy.Orientation = chartmodel.Orientation(r[1])
		xy.XAxis = chartmodel.XAxis{Band: r[2] == 1, Min: chartmodel.Number(unzigzag(r[3])), Max: chartmodel.Number(unzigzag(r[4]))}
		xy.YAxis = chartmodel.YAxis{Min: chartmodel.Number(unzigzag(r[5])), Max: chartmodel.Number(unzigzag(r[6]))}
	case len(r) >= 3 && r[0] == xychartTagPlot:
		xy.Plots = append(xy.Plots, decodeXYPlot(r))
	}
}

func decodeXYPlot(r []int) chartmodel.Plot {
	plot := chartmodel.Plot{Kind: chartmodel.PlotKind(r[1])}
	for at := 3; at+xychartPerPoint <= len(r) && len(plot.Points) < r[2]; at += xychartPerPoint {
		plot.Points = append(plot.Points, chartmodel.Point{
			Present: r[at]&xychartPresent != 0, HasX: r[at]&xychartHasX != 0, Slot: r[at+1] - 1,
			X: chartmodel.Number(unzigzag(r[at+2])), Value: chartmodel.Number(unzigzag(r[at+3])),
		})
	}
	return plot
}

func decodeXYLabel(chart *chartmodel.Chart, l Label) {
	xy := chart.XY
	if rest, ok := strings.CutPrefix(l.ID, "legend."); ok {
		decodeLegendTitle(xy, rest, l.Text)
		return
	}
	if rest, ok := strings.CutPrefix(l.ID, "p"); ok {
		decodePointLabel(xy, rest, l.Text)
		return
	}
	switch {
	case l.ID == "title":
		chart.Title = l.Text
	case l.ID == "x.title":
		xy.XTitle = l.Text
	case l.ID == "y.title":
		xy.YTitle = l.Text
	case xy.XAxis.Band && strings.HasPrefix(l.ID, "x.t"):
		xy.XAxis.Categories = append(xy.XAxis.Categories, l.Text)
	}
}

func decodeLegendTitle(xy *chartmodel.XY, index, text string) {
	if i, err := strconv.Atoi(index); err == nil && i >= 0 && i < len(xy.Plots) {
		xy.Plots[i].Title = text
	}
}

func decodePointLabel(xy *chartmodel.XY, id, text string) {
	plot, point, ok := strings.Cut(id, ".l")
	i, errPlot := strconv.Atoi(plot)
	j, errPoint := strconv.Atoi(point)
	if !ok || errPlot != nil || errPoint != nil || i < 0 || j < 0 || i >= len(xy.Plots) || j >= len(xy.Plots[i].Points) {
		return
	}
	xy.Plots[i].Points[j].Label = text
}

func layoutXYChart(in Input) (scene.Scene, []diag.Diagnostic, error) {
	options := in.Options
	options.Profile = in.Profile
	return chartlayout.Layout(context.Background(), xychartFromInput(in), options)
}
