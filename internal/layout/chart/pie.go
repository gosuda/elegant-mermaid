package chart

import (
	"cmp"
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	pieFullTurn    = 65536
	pieHalfTurn    = 32768
	pieQuarterTurn = 16384

	donutHoleKey    = "donutHole"
	textPositionKey = "textPosition"
	donutHoleMax    = 900
)

type pieConsts struct {
	height, margin, legendRow, legendSize, legendOffset, titlePad, textPosition int64
}

func loadPieConsts() (pieConsts, error) {
	var c pieConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"pie.height", &c.height}, {"pie.margin", &c.margin}, {"pie.legend_row", &c.legendRow},
		{"pie.legend_size", &c.legendSize}, {"pie.legend_offset", &c.legendOffset}, {"pie.title_pad", &c.titlePad},
		{"pie.text_position_m", &c.textPosition},
	} {
		value, err := constant(scene.ProfileVector, row.name)
		if err != nil {
			return pieConsts{}, err
		}
		*row.into = value
	}
	return c, nil
}

type pieSlice struct {
	section int
	start   int64
	sweep   int64
	percent int64
}

type piePlan struct {
	chart        *chartmodel.Chart
	pie          *chartmodel.Pie
	fontFamily   string
	c            pieConsts
	donut        int64
	textPosition int64
	total        int64
	slices       []pieSlice
}

func newPiePlan(m *chartmodel.Chart) (*piePlan, error) {
	if m.Kind != chartmodel.KindPie || m.Pie == nil {
		return nil, errDomain
	}
	c, err := loadPieConsts()
	if err != nil {
		return nil, err
	}
	p := &piePlan{chart: m, pie: m.Pie, c: c, textPosition: c.textPosition}
	values := make([]int64, len(m.Pie.Sections))
	for i, s := range m.Pie.Sections {
		values[i] = int64(s.Value)
		p.total += values[i]
	}
	if err = checkMagnitude(append(values, p.total)...); err != nil {
		return nil, err
	}
	p.configure(m)
	p.slices = pieSlices(values, p.total)
	return p, nil
}

func (p *piePlan) configure(m *chartmodel.Chart) {
	if n, ok := m.Integer(donutHoleKey); ok && n > 0 && n <= donutHoleMax {
		p.donut = n
	}
	if n, ok := m.Integer(textPositionKey); ok && n >= 0 && n <= scale {
		p.textPosition = n
	}
}

func pieSweeps(values []int64, total int64) []int64 {
	sweeps := make([]int64, len(values))
	if total == 0 {
		return sweeps
	}
	rems := make([]int64, len(values))
	var used int64
	for i, v := range values {
		num := v * pieFullTurn
		sweeps[i], rems[i] = geom.FloorDiv(num, total), geom.FloorMod(num, total)
		used += sweeps[i]
	}
	order := make([]int, len(values))
	for i := range order {
		order[i] = i
	}
	slices.SortFunc(order, func(a, b int) int {
		if rems[a] != rems[b] {
			return cmp.Compare(rems[b], rems[a])
		}
		return cmp.Compare(a, b)
	})
	for _, i := range order[:pieFullTurn-used] {
		sweeps[i]++
	}
	return sweeps
}

func pieSlices(values []int64, total int64) []pieSlice {
	var out []pieSlice
	var start int64
	for i, sweep := range pieSweeps(values, total) {
		if sweep > 0 {
			out = append(out, pieSlice{section: i, start: start, sweep: sweep, percent: geom.FloorDiv(200*values[i]+total, 2*total)})
		}
		start += sweep
	}
	return out
}

func (p *piePlan) legendText(section int) string {
	s := p.pie.Sections[section]
	if p.pie.ShowData {
		return s.Label + " [" + FormatNumber(int64(s.Value)) + "]"
	}
	return s.Label
}

type pieLabelKind uint8

const (
	pieLabelTitle pieLabelKind = iota
	pieLabelPercent
	pieLabelLegend
)

type pieLabel struct {
	id, owner, text string
	kind            pieLabelKind
	index           int
}

type pieBox struct {
	id    string
	slice int
}

func pieSliceID(section int) string { return "s" + strconv.Itoa(section) }

func (p *piePlan) boxSpecs() []pieBox {
	out := []pieBox{{id: plotID, slice: -1}}
	for i, s := range p.slices {
		out = append(out, pieBox{id: pieSliceID(s.section), slice: i})
	}
	return out
}

func (p *piePlan) labelSpecs() []pieLabel {
	var out []pieLabel
	if p.chart.Title != "" {
		out = append(out, pieLabel{id: "title", owner: plotID, text: p.chart.Title, kind: pieLabelTitle})
	}
	for i, s := range p.slices {
		if s.percent == 0 {
			continue
		}
		id := pieSliceID(s.section)
		out = append(out, pieLabel{id: id + ".pct", owner: id, text: strconv.FormatInt(s.percent, 10) + "%", kind: pieLabelPercent, index: i})
	}
	for i := range p.pie.Sections {
		out = append(out, pieLabel{id: "legend." + strconv.Itoa(i), owner: plotID, text: p.legendText(i), kind: pieLabelLegend, index: i})
	}
	return out
}

func pieSkeleton(m *chartmodel.Chart) (Skeleton, error) {
	p, err := newPiePlan(m)
	if err != nil {
		return Skeleton{}, err
	}
	var s Skeleton
	for _, b := range p.boxSpecs() {
		parent := plotID
		if b.slice < 0 {
			parent = ""
		}
		s.Boxes = append(s.Boxes, scene.Box{ID: b.id, Role: scene.RoleNode, Parent: parent})
	}
	for _, l := range p.labelSpecs() {
		s.Labels = append(s.Labels, scene.Label{ID: l.id, Owner: l.owner, Text: l.text})
	}
	return s, nil
}
