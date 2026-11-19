package chart

import (
	"strconv"

	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	plotID      = "plot"
	defaultFont = 14
)

type labelKind uint8

const (
	labelTitle labelKind = iota
	labelXTitle
	labelYTitle
	labelXTick
	labelYTick
	labelLegend
	labelPoint
)

type labelSpec struct {
	id, owner, text string
	kind            labelKind
	index           int
	plot            int
}

type boxSpec struct {
	id     string
	plot   int
	point  int
	isLine bool
	isPlot bool
}

func SeriesTitle(index int, title string) string {
	if title != "" {
		return title
	}
	return "Series " + strconv.Itoa(index+1)
}

func seriesBoxID(plot int) string { return "p" + strconv.Itoa(plot) }

func barBoxID(plot, point int) string { return seriesBoxID(plot) + ".b" + strconv.Itoa(point) }

func pointLabelID(plot, point int) string { return seriesBoxID(plot) + ".l" + strconv.Itoa(point) }

func boxSpecs(xy *chartmodel.XY) []boxSpec {
	specs := []boxSpec{{id: plotID, isPlot: true}}
	for i, plot := range xy.Plots {
		if plot.Kind == chartmodel.PlotLine {
			specs = append(specs, boxSpec{id: seriesBoxID(i), plot: i, isLine: true})
			continue
		}
		for j, point := range plot.Points {
			if point.Present {
				specs = append(specs, boxSpec{id: barBoxID(i, j), plot: i, point: j})
			}
		}
	}
	return specs
}

func (a *axis) tickSpecs(kind labelKind, prefix string) []labelSpec {
	out := make([]labelSpec, 0, len(a.labels))
	for k, text := range a.labels {
		out = append(out, labelSpec{id: prefix + ".t" + strconv.Itoa(k), owner: plotID, text: text, kind: kind, index: k})
	}
	return out
}

func labelSpecs(m *chartmodel.Chart, x, y *axis) []labelSpec {
	var out []labelSpec
	add := func(id, text string, kind labelKind) {
		if text != "" {
			out = append(out, labelSpec{id: id, owner: plotID, text: text, kind: kind})
		}
	}
	add("title", m.Title, labelTitle)
	add("x.title", m.XY.XTitle, labelXTitle)
	add("y.title", m.XY.YTitle, labelYTitle)
	out = append(out, x.tickSpecs(labelXTick, "x")...)
	out = append(out, y.tickSpecs(labelYTick, "y")...)
	for i, plot := range m.XY.Plots {
		out = append(out, labelSpec{id: "legend." + strconv.Itoa(i), owner: plotID, text: SeriesTitle(i, plot.Title), kind: labelLegend, plot: i})
	}
	for i, plot := range m.XY.Plots {
		for j, point := range plot.Points {
			if point.Present && point.Label != "" {
				out = append(out, labelSpec{id: pointLabelID(i, j), owner: seriesBoxID(i), text: point.Label, kind: labelPoint, plot: i, index: j})
			}
		}
	}
	return out
}

func (p *xyPlan) dumpBoxes() []scene.Box {
	out := make([]scene.Box, len(p.boxes))
	for i, b := range p.boxes {
		parent := plotID
		if b.isPlot {
			parent = ""
		}
		out[i] = scene.Box{ID: b.id, Role: scene.RoleNode, Parent: parent}
		if p.laidOut {
			out[i].Rect = p.boxRects[i]
		}
	}
	return out
}

func (p *xyPlan) dumpLabels() []scene.Label {
	out := make([]scene.Label, len(p.specs))
	for i, s := range p.specs {
		out[i] = scene.Label{ID: s.id, Owner: s.owner, Text: s.text}
		if p.laidOut {
			out[i].Rect = p.labelRects[i]
			out[i].Lines = p.labelLines[i]
		}
	}
	return out
}
