package chart

import (
	"math/bits"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/civil"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	ganttTaskFont    = 12
	ganttSecFont     = 14
	ganttTickFont    = 10
	ganttDefaultFm   = "%Y-%m-%d"
	ganttDefaultDay  = "sunday"
	ganttMaxConfigPx = 1 << 25
)

type ganttConsts struct {
	width, barH, rowGap, topPad, gutter, sidePad, axisH int64
	tickLen, tickGap, titlePad, labelGap, sectionPad    int64
	vertW, tickCap, estimateCap, excludeYears           int64
	edge                                                int64
}

func loadGanttConsts(profile scene.Profile, m *chartmodel.Chart) (ganttConsts, error) {
	var c ganttConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"gantt.width", &c.width}, {"gantt.bar_height", &c.barH}, {"gantt.row_gap", &c.rowGap},
		{"gantt.top_pad", &c.topPad}, {"gantt.label_gutter", &c.gutter}, {"gantt.side_pad", &c.sidePad},
		{"gantt.axis_height", &c.axisH}, {"gantt.tick_length", &c.tickLen}, {"gantt.tick_label_gap", &c.tickGap},
		{"gantt.title_pad", &c.titlePad}, {"gantt.label_gap", &c.labelGap}, {"gantt.section_pad", &c.sectionPad},
		{"gantt.vert_width", &c.vertW}, {"gantt.tick_cap", &c.tickCap}, {"gantt.tick_estimate_cap", &c.estimateCap},
		{"gantt.exclude_years_max", &c.excludeYears},
	} {
		value, err := constant(profile, row.name)
		if err != nil {
			return ganttConsts{}, err
		}
		*row.into = value
	}
	if profile == scene.ProfileCell {
		c.edge = 1
	}
	for _, row := range []struct {
		key    string
		into   *int64
		cellPx int64
	}{
		{"barHeight", &c.barH, 16}, {"barGap", &c.rowGap, 16}, {"topPadding", &c.topPad, 16},
		{"leftPadding", &c.gutter, 8}, {"rightPadding", &c.sidePad, 8},
	} {
		n, ok := m.Integer(row.key)
		if !ok {
			continue
		}
		if n < -ganttMaxConfigPx || n > ganttMaxConfigPx {
			return ganttConsts{}, ErrOverflow
		}
		*row.into = canvasSide(profile, n, 64, row.cellPx)
	}
	return c, nil
}

type ganttBoxKind uint8

const (
	ganttBoxPlot ganttBoxKind = iota
	ganttBoxSection
	ganttBoxTask
	ganttBoxVert
)

type ganttBox struct {
	id    string
	kind  ganttBoxKind
	index int
	row   int
}

type ganttLabelKind uint8

const (
	ganttLabelTitle ganttLabelKind = iota
	ganttLabelSection
	ganttLabelTask
	ganttLabelTick
	ganttLabelTopTick
)

type ganttLabel struct {
	id, owner, text string
	kind            ganttLabelKind
	index           int
}

type ganttPlan struct {
	m          *chartmodel.Chart
	g          *chartmodel.Gantt
	o          scene.Options
	c          ganttConsts
	cell       bool
	boxes      []ganttBox
	labels     []ganttLabel
	d0, d1     int64
	ticks      []int64
	tickText   []string
	capped     bool
	width      int64
	height     int64
	pitch      int64
	rows       int64
	plot       rect
	texts      []textBox
	boxRects   []geom.Rect
	labelRects []geom.Rect
	labelLines [][]string
	shown      []bool
	aligns     []scene.Align
	chips      []bool
	laidOut    bool
}

func ganttBoxID(kind ganttBoxKind, index int) string {
	switch kind {
	case ganttBoxSection:
		return "s" + strconv.Itoa(index)
	case ganttBoxTask, ganttBoxVert:
		return "t" + strconv.Itoa(index)
	}
	return plotID
}

func newGanttPlan(m *chartmodel.Chart, o scene.Options) (*ganttPlan, error) {
	if m.Gantt == nil {
		return nil, errDomain
	}
	c, err := loadGanttConsts(o.Profile, m)
	if err != nil {
		return nil, err
	}
	p := &ganttPlan{m: m, g: m.Gantt, o: o, c: c, cell: o.Profile == scene.ProfileCell}
	if err = p.checkRows(); err != nil {
		return nil, err
	}
	p.pitch = c.barH + c.rowGap
	p.d0, p.d1 = p.domain()
	p.computeTicks()
	p.buildBoxes()
	p.buildLabels()
	return p, nil
}

func (p *ganttPlan) checkTasks() error {
	for _, t := range p.g.Tasks {
		for _, v := range []int64{t.Start, t.End, t.RenderEnd} {
			if v < -civil.MaxAbsSeconds || v > civil.MaxAbsSeconds {
				return ErrOverflow
			}
		}
		if t.Section < -1 || t.Section >= len(p.g.Sections) {
			return errDomain
		}
	}
	return nil
}

func (p *ganttPlan) checkRows() error {
	if err := p.checkTasks(); err != nil {
		return err
	}
	for _, row := range p.g.Rows {
		limit := len(p.g.Tasks)
		if row.Kind == chartmodel.GanttRowSection {
			limit = len(p.g.Sections)
		}
		if row.Index < 0 || row.Index >= limit {
			return errDomain
		}
	}
	return nil
}

func (p *ganttPlan) domain() (lo, hi int64) {
	if len(p.g.Tasks) == 0 {
		return 0, civil.SecondsPerDay
	}
	lo, hi = p.g.Tasks[0].Start, p.g.Tasks[0].End
	for _, t := range p.g.Tasks[1:] {
		lo, hi = min(lo, t.Start), max(hi, t.End)
	}
	return lo, hi
}

func (p *ganttPlan) buildBoxes() {
	p.boxes = []ganttBox{{id: plotID, kind: ganttBoxPlot, row: -1}}
	for k, row := range p.g.Rows {
		kind := ganttBoxTask
		if row.Kind == chartmodel.GanttRowSection {
			kind = ganttBoxSection
		}
		p.boxes = append(p.boxes, ganttBox{id: ganttBoxID(kind, row.Index), kind: kind, index: row.Index, row: k})
	}
	for i, t := range p.g.Tasks {
		if t.Vert {
			p.boxes = append(p.boxes, ganttBox{id: ganttBoxID(ganttBoxVert, i), kind: ganttBoxVert, index: i, row: -1})
		}
	}
	p.rows = int64(len(p.g.Rows))
}

func (p *ganttPlan) buildLabels() {
	add := func(label ganttLabel) {
		if label.text != "" {
			p.labels = append(p.labels, label)
		}
	}
	add(ganttLabel{id: "title", owner: plotID, text: p.m.Title, kind: ganttLabelTitle})
	for _, b := range p.boxes {
		switch b.kind {
		case ganttBoxSection:
			add(ganttLabel{id: b.id + ".label", owner: b.id, text: p.g.Sections[b.index], kind: ganttLabelSection, index: b.index})
		case ganttBoxTask, ganttBoxVert:
			add(ganttLabel{id: b.id + ".label", owner: b.id, text: p.g.Tasks[b.index].Label, kind: ganttLabelTask, index: b.index})
		}
	}
	for k, text := range p.tickText {
		add(ganttLabel{id: "x.t" + strconv.Itoa(k), owner: plotID, text: text, kind: ganttLabelTick, index: k})
	}
	if p.g.TopAxis {
		for k, text := range p.tickText {
			add(ganttLabel{id: "xt.t" + strconv.Itoa(k), owner: plotID, text: text, kind: ganttLabelTopTick, index: k})
		}
	}
}

func (p *ganttPlan) dumpBoxes() []scene.Box {
	out := make([]scene.Box, len(p.boxes))
	for i, b := range p.boxes {
		parent := plotID
		if b.kind == ganttBoxPlot {
			parent = ""
		}
		out[i] = scene.Box{ID: b.id, Role: scene.RoleNode, Parent: parent}
		if p.laidOut {
			out[i].Rect = p.boxRects[i]
		}
	}
	return out
}

func (p *ganttPlan) dumpLabels() []scene.Label {
	out := make([]scene.Label, len(p.labels))
	for i, l := range p.labels {
		out[i] = scene.Label{ID: l.id, Owner: l.owner, Text: l.text}
		if p.laidOut {
			out[i].Rect = p.labelRects[i]
			out[i].Lines = p.labelLines[i]
		}
	}
	return out
}

func mulChecked(a, b int64) (int64, error) {
	negative := (a < 0) != (b < 0)
	ua, ub := uint64(a), uint64(b)
	if a < 0 {
		ua = -ua
	}
	if b < 0 {
		ub = -ub
	}
	hi, lo := bits.Mul64(ua, ub)
	if hi != 0 || lo > 1<<63-1 {
		return 0, ErrOverflow
	}
	if negative {
		return -int64(lo), nil
	}
	return int64(lo), nil
}

func (p *ganttPlan) timeX(v int64) (int64, error) {
	r0, r1 := p.c.gutter, p.c.width-p.c.sidePad
	if p.d1 == p.d0 {
		return geom.FloorDiv(r0+r1, 2), nil
	}
	product, err := mulChecked(v-p.d0, r1-r0)
	if err != nil {
		return 0, err
	}
	return r0 + geom.FloorDiv(product, p.d1-p.d0), nil
}

func (p *ganttPlan) axisY() int64 { return p.c.topPad + p.rows*p.pitch }

func (p *ganttPlan) topAxisY() int64 { return p.c.topPad - p.c.edge }

func (p *ganttPlan) rowTop(row int) int64 { return p.c.topPad + int64(row)*p.pitch }

func (p *ganttPlan) metric(role measure.Role, size int32) measure.Metric {
	if p.cell {
		return measure.CellMetric()
	}
	return measure.Metric{Profile: measure.ProfileVector, SizePx: size, Weight: role.Weight()}
}

func (p *ganttPlan) lineHeight(role measure.Role, size int32) int64 {
	if p.cell {
		return 1
	}
	return measure.RoundHalfUp(int64(size)*64*int64(role.LineHeightPx()), int64(role.SizePx()))
}

func (p *ganttPlan) styleOf(l ganttLabel) (measure.Role, int32) {
	switch l.kind {
	case ganttLabelTitle:
		return measure.RoleTitle, measure.RoleTitle.SizePx()
	case ganttLabelSection:
		return measure.RoleLabel, ganttSecFont
	case ganttLabelTask:
		return measure.RoleLabel, ganttTaskFont
	}
	return measure.RoleLabel, ganttTickFont
}

func (p *ganttPlan) measureAll() error {
	p.texts = make([]textBox, len(p.labels))
	for i, l := range p.labels {
		role, size := p.styleOf(l)
		lines, err := measure.StyledLines(l.text, geom.I32Max, p.metric(role, size))
		if err != nil {
			return err
		}
		var widest int64
		for _, line := range lines {
			widest = max(widest, int64(line.Width))
		}
		p.texts[i] = textBox{lines: lines, w: widest, h: int64(len(lines)) * p.lineHeight(role, size)}
	}
	return nil
}

func layoutGantt(m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newGanttPlan(m, o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.measureAll(); err != nil {
		return scene.Scene{}, nil, err
	}
	p.width = p.c.width
	p.height = p.c.topPad + p.rows*p.pitch + p.c.axisH
	p.plot = rect{0, p.c.topPad, p.width, p.rows * p.pitch}
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

func ganttSkeleton(m *chartmodel.Chart) (Skeleton, error) {
	p, err := newGanttPlan(m, scene.Options{})
	if err != nil {
		return Skeleton{}, err
	}
	return Skeleton{Boxes: p.dumpBoxes(), Labels: p.dumpLabels()}, nil
}
