package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type consts struct {
	width, height, reserved, barPad, barRatio, outerMax int64
	axisLine, axisTitlePad, padX, padY, tickLen         int64
	titlePad, legendPad, legendMarker, markerGap        int64
	itemGap, pointOffset, pointSize, edge               int64
}

func loadConsts(profile scene.Profile, m *chartmodel.Chart) (consts, error) {
	var c consts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"xychart.width", &c.width}, {"xychart.height", &c.height}, {"xychart.plot_reserved_percent", &c.reserved},
		{"xychart.bar_padding_m", &c.barPad}, {"xychart.bar_width_ratio_m", &c.barRatio}, {"xychart.label_outer_max_m", &c.outerMax},
		{"xychart.axis_line", &c.axisLine}, {"xychart.axis_title_pad", &c.axisTitlePad}, {"xychart.label_pad_x", &c.padX},
		{"xychart.label_pad_y", &c.padY}, {"xychart.tick_length", &c.tickLen}, {"xychart.title_pad", &c.titlePad},
		{"xychart.legend_pad", &c.legendPad}, {"xychart.legend_marker", &c.legendMarker}, {"xychart.legend_marker_gap", &c.markerGap},
		{"xychart.legend_item_gap", &c.itemGap}, {"xychart.point_label_offset", &c.pointOffset}, {"xychart.point_label_size", &c.pointSize},
	} {
		value, err := constant(profile, row.name)
		if err != nil {
			return consts{}, err
		}
		*row.into = value
	}
	if profile == scene.ProfileCell {
		c.edge = 1
	}
	c.applyConfig(profile, m)
	return c, nil
}

func (c *consts) applyConfig(profile scene.Profile, m *chartmodel.Chart) {
	if n, ok := m.Integer("width"); ok {
		c.width = canvasSide(profile, n, 64, 8)
	}
	if n, ok := m.Integer("height"); ok {
		c.height = canvasSide(profile, n, 64, 16)
	}
	if n, ok := m.Integer("plotReservedSpacePercent"); ok {
		c.reserved = n
	}
}

func canvasSide(profile scene.Profile, px, vectorUnits, cellPx int64) int64 {
	if profile == scene.ProfileCell {
		return measure.CeilDiv(px, cellPx)
	}
	return px * vectorUnits
}

type textBox struct {
	lines []measure.StyledLine
	w, h  int64
}

type xyPlan struct {
	m          *chartmodel.Chart
	xy         *chartmodel.XY
	o          scene.Options
	c          consts
	cell       bool
	x, y       axis
	capped     bool
	boxes      []boxSpec
	specs      []labelSpec
	texts      []textBox
	width      int64
	height     int64
	plot       rect
	titleShown bool
	sideTitle  int
	sideShown  bool
	legend     rect
	legendOn   bool
	legendLH   int64
	legendRows int64
	boxRects   []geom.Rect
	labelRects []geom.Rect
	labelLines [][]string
	shown      []bool
	aligns     []scene.Align
	titleH     int64
	laidOut    bool
}

func newXYPlan(m *chartmodel.Chart, o scene.Options) (*xyPlan, error) {
	c, err := loadConsts(o.Profile, m)
	if err != nil {
		return nil, err
	}
	xy := m.XY
	x, y, capped, err := newAxes(xy)
	if err != nil {
		return nil, err
	}
	if err = checkPoints(xy); err != nil {
		return nil, err
	}
	p := &xyPlan{m: m, xy: xy, o: o, c: c, cell: o.Profile == scene.ProfileCell, x: x, y: y, capped: capped, sideTitle: -1}
	p.x.position, p.y.position = posBottom, posLeft
	if xy.Orientation == chartmodel.OrientationHorizontal {
		p.x.position, p.y.position = posLeft, posTop
	}
	p.x.title, p.y.title = xy.XTitle, xy.YTitle
	p.x.showLabels, p.y.showLabels = true, true
	p.x.fontSize, p.y.fontSize = defaultFont, defaultFont
	if show, ok := m.Bool("xAxis.showLabel"); ok {
		p.x.showLabels = show
	}
	if size, ok := m.Integer("xAxis.labelFontSize"); ok {
		p.x.fontSize = int32(size)
	}
	p.boxes = boxSpecs(xy)
	p.specs = labelSpecs(m, &p.x, &p.y)
	return p, nil
}

func checkPoints(xy *chartmodel.XY) error {
	for _, plot := range xy.Plots {
		for _, point := range plot.Points {
			if err := checkMagnitude(int64(point.Value), int64(point.X)); err != nil {
				return err
			}
		}
	}
	return nil
}

func (p *xyPlan) horizontal() bool { return p.xy.Orientation == chartmodel.OrientationHorizontal }

func (p *xyPlan) styleOf(s labelSpec) (measure.Role, int32) {
	switch s.kind {
	case labelTitle:
		return measure.RoleTitle, measure.RoleTitle.SizePx()
	case labelXTick:
		return measure.RoleLabel, p.x.fontSize
	case labelPoint:
		return measure.RoleBody, int32(p.c.pointSize / 64)
	}
	return measure.RoleLabel, defaultFont
}

func (p *xyPlan) lineHeight(role measure.Role, size int32) int64 {
	if p.cell {
		return 1
	}
	return measure.RoundHalfUp(int64(size)*64*int64(role.LineHeightPx()), int64(role.SizePx()))
}

func (p *xyPlan) metric(role measure.Role, size int32) measure.Metric {
	if p.cell {
		return measure.CellMetric()
	}
	return measure.Metric{Profile: measure.ProfileVector, SizePx: size, Weight: role.Weight(), FontFamily: p.o.FontFamily != ""}
}

func (p *xyPlan) measureText(text string, role measure.Role, size int32) (textBox, error) {
	lines, err := measure.StyledLines(text, geom.I32Max, p.metric(role, size))
	if err != nil {
		return textBox{}, err
	}
	var widest int64
	for _, line := range lines {
		widest = max(widest, int64(line.Width))
	}
	return textBox{lines: lines, w: widest, h: int64(len(lines)) * p.lineHeight(role, size)}, nil
}

func (p *xyPlan) measureAll() error {
	p.texts = make([]textBox, len(p.specs))
	for i, s := range p.specs {
		role, size := p.styleOf(s)
		box, err := p.measureText(s.text, role, size)
		if err != nil {
			return err
		}
		p.texts[i] = box
	}
	return nil
}

func (p *xyPlan) find(kind labelKind) (int, bool) {
	for i, s := range p.specs {
		if s.kind == kind {
			return i, true
		}
	}
	return 0, false
}

func (p *xyPlan) tickExtent(kind labelKind) (w, h int64) {
	for i, s := range p.specs {
		if s.kind == kind {
			w, h = max(w, p.texts[i].w), max(h, p.texts[i].h)
		}
	}
	return w, h
}

func layoutXY(m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newXYPlan(m, o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.measureAll(); err != nil {
		return scene.Scene{}, nil, err
	}
	p.arrange()
	if err = p.place(); err != nil {
		return scene.Scene{}, nil, err
	}
	w, err := i32(p.width)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	h, err := i32(p.height)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: string(m.Kind), Options: o, Canvas: geom.Size{W: w, H: h}, Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}
	dump.Options.Direction = scene.DirectionTB
	groups, err := p.groups()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	var diagnostics []diag.Diagnostic
	if p.capped {
		diagnostics = append(diagnostics, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	return scene.Scene{Dump: dump, Groups: groups}, diagnostics, nil
}
