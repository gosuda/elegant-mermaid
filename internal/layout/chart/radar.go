package chart

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	radarPlotID  = "plot"
	radarTitleID = "title"
	q15One       = 32768
	quarterTurn  = 16384
	fullTurn     = 65536
	tickScale    = 1000
	radarTicksAt = 32 * tickScale
	radarFont    = 14
	radarSeries  = 12
)

type radarConsts struct {
	width, height, margin, gapX, gapY, legendRow int64
	tension, marker, markerGap, anchor           int64
	marginTop, marginRight                       int64
}

func loadRadarConsts(m *chartmodel.Chart) (radarConsts, error) {
	var c radarConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"radar.width", &c.width}, {"radar.height", &c.height}, {"radar.margin", &c.margin},
		{"radar.label_gap_x", &c.gapX}, {"radar.label_gap_y", &c.gapY}, {"radar.legend_row", &c.legendRow},
		{"radar.curve_tension", &c.tension}, {"radar.legend_marker", &c.marker},
		{"radar.legend_text_gap", &c.markerGap}, {"radar.anchor_q15", &c.anchor},
	} {
		value, err := constant(scene.ProfileVector, row.name)
		if err != nil {
			return radarConsts{}, err
		}
		*row.into = value
	}
	c.marginTop, c.marginRight = c.margin, c.margin
	for _, row := range []struct {
		key  string
		into *int64
		unit int64
	}{
		{"width", &c.width, 64}, {"height", &c.height, 64}, {"marginTop", &c.marginTop, 64},
		{"marginRight", &c.marginRight, 64}, {"curveTension", &c.tension, 1},
	} {
		if n, ok := m.Integer(row.key); ok {
			*row.into = n * row.unit
		}
	}
	return c, nil
}

type radarLabelKind uint8

const (
	radarTitle radarLabelKind = iota
	radarAxis
	radarLegend
)

type radarLabel struct {
	id, text string
	kind     radarLabelKind
	index    int
}

type point struct{ x, y int64 }

type radarPlan struct {
	m          *chartmodel.Chart
	r          *chartmodel.Radar
	c          radarConsts
	radius     int64
	extent     int64
	rings      []int64
	drawn      []int
	lo, hi     int64
	labels     []radarLabel
	texts      []textBox
	rects      []rect
	shown      []bool
	aligns     []scene.Align
	frame      rect
	plot       rect
	curves     [][]point
	markers    []rect
	dx, dy     int64
	canvas     geom.Size
	boxRects   []geom.Rect
	labelRects []geom.Rect
	placed     bool
}

func newRadarPlan(m *chartmodel.Chart) (*radarPlan, error) {
	c, err := loadRadarConsts(m)
	if err != nil {
		return nil, err
	}
	p := &radarPlan{m: m, r: m.Radar, c: c, radius: geom.FloorDiv(min(c.width, c.height), 2)}
	if err = p.resolveRange(); err != nil {
		return nil, err
	}
	p.rings = ringRadii(p.radius, int64(p.r.Ticks))
	p.extent = p.radius
	for _, ring := range p.rings {
		p.extent = max(p.extent, ring)
	}
	p.drawn = p.drawnCurves()
	p.labels = radarLabels(m)
	return p, nil
}

func (p *radarPlan) resolveRange() error {
	r := p.r
	hi, seen := int64(r.Max), r.HasMax
	for _, curve := range r.Curves {
		for _, v := range curve.Values {
			if err := checkMagnitude(int64(v)); err != nil {
				return err
			}
			if !seen || (!r.HasMax && int64(v) > hi) {
				hi, seen = int64(v), true
			}
		}
	}
	p.lo, p.hi = int64(r.Min), hi
	if !seen {
		p.hi = p.lo
	}
	if err := checkMagnitude(p.lo, p.hi); err != nil {
		return err
	}
	if p.hi-p.lo > int64(geom.I32Max) {
		return ErrOverflow
	}
	return nil
}

func ringRadii(radius, ticks int64) []int64 {
	ticks = Clamp(ticks, 0, radarTicksAt)
	count := geom.FloorDiv(ticks+tickScale-1, tickScale)
	out := make([]int64, 0, count)
	for i := range count {
		out = append(out, geom.FloorDiv(radius*(i+1)*tickScale, ticks))
	}
	return out
}

func (p *radarPlan) drawnCurves() []int {
	var out []int
	if len(p.r.Axes) == 0 || p.hi <= p.lo {
		return out
	}
	for i, curve := range p.r.Curves {
		if len(curve.Values) == len(p.r.Axes) {
			out = append(out, i)
		}
	}
	return out
}

func radarCurveID(i int) string { return "c" + strconv.Itoa(i) }

func radarAxisID(j int) string { return "axis." + strconv.Itoa(j) }

func radarLegendID(i int) string { return "legend." + strconv.Itoa(i) }

func radarLabels(m *chartmodel.Chart) []radarLabel {
	var out []radarLabel
	if m.Title != "" {
		out = append(out, radarLabel{id: radarTitleID, text: m.Title, kind: radarTitle})
	}
	for j, axis := range m.Radar.Axes {
		out = append(out, radarLabel{id: radarAxisID(j), text: axis, kind: radarAxis, index: j})
	}
	for i, curve := range m.Radar.Curves {
		out = append(out, radarLabel{id: radarLegendID(i), text: curve.Label, kind: radarLegend, index: i})
	}
	return out
}

func (p *radarPlan) boxIDs() []string {
	ids := []string{radarPlotID}
	for _, i := range p.drawn {
		ids = append(ids, radarCurveID(i))
	}
	return ids
}

func (p *radarPlan) dumpBoxes() []scene.Box {
	ids := p.boxIDs()
	out := make([]scene.Box, len(ids))
	for i, id := range ids {
		out[i] = scene.Box{ID: id, Role: scene.RoleNode}
		if i > 0 {
			out[i].Parent = radarPlotID
		}
		if p.placed {
			out[i].Rect = p.boxRects[i]
		}
	}
	return out
}

func (p *radarPlan) dumpLabels() []scene.Label {
	out := make([]scene.Label, len(p.labels))
	for i, l := range p.labels {
		out[i] = scene.Label{ID: l.id, Owner: radarPlotID, Text: l.text}
		if !p.placed {
			continue
		}
		out[i].Lines = []string{}
		if !p.shown[i] {
			continue
		}
		out[i].Rect = p.labelRects[i]
		for _, line := range p.texts[i].lines {
			out[i].Lines = append(out[i].Lines, line.Text)
		}
	}
	return out
}

func radarRole(l radarLabel) (measure.Role, int32) {
	if l.kind == radarTitle {
		return measure.RoleTitle, measure.RoleTitle.SizePx()
	}
	return measure.RoleLabel, radarFont
}

func (p *radarPlan) measureAll() error {
	p.texts = make([]textBox, len(p.labels))
	for i, l := range p.labels {
		role, size := radarRole(l)
		lines, err := measure.StyledLines(l.text, geom.I32Max, measure.Metric{Profile: measure.ProfileVector, SizePx: size, Weight: role.Weight()})
		if err != nil {
			return err
		}
		var widest int64
		for _, line := range lines {
			widest = max(widest, int64(line.Width))
		}
		lineH := measure.RoundHalfUp(int64(size)*64*int64(role.LineHeightPx()), int64(role.SizePx()))
		p.texts[i] = textBox{lines: lines, w: widest, h: int64(len(lines)) * lineH}
	}
	return nil
}

func layoutRadar(m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newRadarPlan(m)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.measureAll(); err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.place(); err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: string(m.Kind), Options: o, Canvas: p.canvas, Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}
	dump.Options.Direction = scene.DirectionTB
	groups, err := p.groups()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: groups}, nil, nil
}

func radarSkeleton(m *chartmodel.Chart) (Skeleton, error) {
	p, err := newRadarPlan(m)
	if err != nil {
		return Skeleton{}, err
	}
	return Skeleton{Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}, nil
}
