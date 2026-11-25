package chart

import (
	"cmp"
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	sankeyUnitsPerPx = 64
	valueBreak       = "<br>"
	hundredthsStep   = 10

	cellColumnUnits = 512
)

type sankeyConsts struct {
	width, height, nodeWidth, padding, iterations, labelGap int64
}

func SankeyNodeID(i int) string { return "n" + strconv.Itoa(i) }

func SankeyLinkID(i int) string { return "l" + strconv.Itoa(i) }

func sankeyLabelID(i int) string { return SankeyNodeID(i) + ".label" }

func showValues(m *chartmodel.Chart) bool {
	v, ok := m.Bool("showValues")
	return !ok || v
}

func loadSankeyConsts(m *chartmodel.Chart) (sankeyConsts, error) {
	var c sankeyConsts
	var valuePad int64
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"sankey.width", &c.width}, {"sankey.height", &c.height}, {"sankey.node_width", &c.nodeWidth},
		{"sankey.node_padding", &c.padding}, {"sankey.show_values_pad", &valuePad},
		{"sankey.iterations", &c.iterations}, {"sankey.label_gap", &c.labelGap},
	} {
		value, err := constant(scene.ProfileVector, row.name)
		if err != nil {
			return sankeyConsts{}, err
		}
		*row.into = value
	}
	if showValues(m) {
		c.padding += valuePad
	}
	if n, ok := m.Integer("width"); ok {
		c.width = n * sankeyUnitsPerPx
	}
	if n, ok := m.Integer("height"); ok {
		c.height = n * sankeyUnitsPerPx
	}
	return c, nil
}

func SankeyLabels(m *chartmodel.Chart) []string {
	s := m.Sankey
	in, out := make([]int64, len(s.Nodes)), make([]int64, len(s.Nodes))
	for _, l := range s.Links {
		if l.Kind == chartmodel.ValueFinite {
			out[l.Source] += int64(l.Value)
			in[l.Target] += int64(l.Value)
		}
	}
	show := showValues(m)
	labels := make([]string, len(s.Nodes))
	for i, n := range s.Nodes {
		labels[i] = labelText(n.ID, max(in[i], out[i]), show)
	}
	return labels
}

func labelText(id string, value int64, show bool) string {
	id = strings.ReplaceAll(id, "\n", " ")
	if !show {
		return id
	}
	hundredths := geom.FloorDiv(value+hundredthsStep/2, hundredthsStep)
	return id + valueBreak + FormatNumber(hundredths*hundredthsStep)
}

func sankeySkeleton(m *chartmodel.Chart) Skeleton {
	var sk Skeleton
	for i, n := range m.Sankey.Nodes {
		sk.Boxes = append(sk.Boxes, scene.Box{ID: SankeyNodeID(i), Role: scene.RoleNode})
		if n.Label != "" {
			sk.Labels = append(sk.Labels, scene.Label{ID: sankeyLabelID(i), Owner: SankeyNodeID(i), Text: n.Label})
		}
	}
	return sk
}

type sankeyText struct {
	lines []measure.Line
	w, h  int64
	cells int64
}

func measureSankeyLabel(text, fontFamily string) (sankeyText, error) {
	role := measure.RoleLabel
	metric := measure.Metric{Profile: measure.ProfileVector, SizePx: role.SizePx(), Weight: role.Weight(), FontFamily: fontFamily != ""}
	lines, err := measure.Wrap(text, geom.I32Max, metric)
	if err != nil {
		return sankeyText{}, err
	}
	var widest, cells int64
	for _, l := range lines {
		width, err := measure.CellWidth(l.Text)
		if err != nil {
			return sankeyText{}, err
		}
		widest = max(widest, int64(l.Width))
		cells = max(cells, int64(width)*cellColumnUnits)
	}
	lh := measure.RoundHalfUp(int64(role.SizePx())*sankeyUnitsPerPx*int64(role.LineHeightPx()), int64(role.SizePx()))
	return sankeyText{lines: lines, w: widest, h: int64(len(lines)) * lh, cells: cells}, nil
}

type sankeyPlan struct {
	m          *chartmodel.Chart
	s          *chartmodel.Sankey
	fontFamily string
	c          sankeyConsts
	flow       *flow
	width      int64
	height     int64
	nodes      []rect
	texts      []*sankeyText
	places     []rect
	aligns     []scene.Align
}

func layoutSankey(m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newSankeyPlan(m)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	p.fontFamily = o.FontFamily
	if err = p.arrange(); err != nil {
		return scene.Scene{}, nil, err
	}
	dump, err := p.dump(o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	groups, err := p.groups()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: groups}, nil, nil
}

func newSankeyPlan(m *chartmodel.Chart) (*sankeyPlan, error) {
	c, err := loadSankeyConsts(m)
	if err != nil {
		return nil, err
	}
	f, err := newFlow(m.Sankey)
	if err != nil {
		return nil, err
	}
	f.extent, f.pad, f.iterations = c.height, c.padding, int(c.iterations)
	return &sankeyPlan{m: m, s: m.Sankey, c: c, flow: f, width: c.width, height: c.height}, nil
}

func (p *sankeyPlan) arrange() error {
	name, _ := p.m.String("nodeAlignment")
	if err := p.flow.run(parseAlignment(name)); err != nil {
		return err
	}
	p.placeNodes()
	if err := p.placeLabels(); err != nil {
		return err
	}
	return p.normalizeCanvas()
}

func (p *sankeyPlan) placeNodes() {
	maxDepth := 0
	for _, n := range p.flow.nodes {
		maxDepth = max(maxDepth, n.depth)
	}
	span := p.c.width - p.c.nodeWidth
	p.nodes = make([]rect, len(p.flow.nodes))
	for i, n := range p.flow.nodes {
		x := int64(0)
		if maxDepth > 0 {
			x = geom.FloorDiv(int64(n.layer)*span, int64(maxDepth))
		}
		p.nodes[i] = rect{x: x, y: n.y0, w: p.c.nodeWidth, h: n.y1 - n.y0}
	}
}

func (p *sankeyPlan) placeLabels() error {
	p.texts = make([]*sankeyText, len(p.nodes))
	p.places = make([]rect, len(p.nodes))
	p.aligns = make([]scene.Align, len(p.nodes))
	var labelled []int
	for i, n := range p.s.Nodes {
		if n.Label == "" {
			continue
		}
		text, err := measureSankeyLabel(n.Label, p.fontFamily)
		if err != nil {
			return err
		}
		p.texts[i] = &text
		p.places[i], p.aligns[i] = p.labelRect(p.nodes[i], text)
		labelled = append(labelled, i)
	}
	p.separateLabels(labelled)
	for _, i := range labelled {
		p.width = max(p.width, p.places[i].x+p.places[i].w)
		p.height = max(p.height, p.places[i].y+p.places[i].h)
	}
	return nil
}

func (p *sankeyPlan) normalizeCanvas() error {
	minX, minY, maxX, maxY := int64(0), int64(0), p.width, p.height
	a := arith{}
	include := func(r rect) {
		minX, minY = min(minX, r.x), min(minY, r.y)
		maxX, maxY = max(maxX, a.add(r.x, r.w)), max(maxY, a.add(r.y, r.h))
	}
	for _, r := range p.nodes {
		include(r)
	}
	for i, text := range p.texts {
		if text != nil {
			include(p.places[i])
		}
	}
	for _, link := range p.flow.links {
		minY = min(minY, link.y0, link.y1)
		maxY = max(maxY, link.y0, link.y1)
	}
	dx, dy := a.mul(-1, minX), a.mul(-1, minY)
	for i := range p.nodes {
		p.nodes[i].x, p.nodes[i].y = a.add(p.nodes[i].x, dx), a.add(p.nodes[i].y, dy)
		p.places[i].x, p.places[i].y = a.add(p.places[i].x, dx), a.add(p.places[i].y, dy)
	}
	for i := range p.flow.links {
		p.flow.links[i].y0 = a.add(p.flow.links[i].y0, dy)
		p.flow.links[i].y1 = a.add(p.flow.links[i].y1, dy)
	}
	p.width, p.height = a.add(maxX, dx), a.add(maxY, dy)
	if a.failed {
		return ErrOverflow
	}
	return nil
}

func (p *sankeyPlan) separateLabels(labelled []int) {
	slices.SortStableFunc(labelled, func(a, b int) int { return cmp.Compare(p.places[a].y, p.places[b].y) })
	for k, i := range labelled {
		for moved := true; moved; {
			moved = false
			for _, j := range labelled[:k] {
				if p.reach(i).meets(p.reach(j)) {
					p.places[i].y = p.places[j].y + p.places[j].h
					moved = true
				}
			}
		}
	}
}

func (p *sankeyPlan) reach(i int) rect {
	place := p.places[i]
	width := max(place.w, p.texts[i].cells) + 2*cellColumnUnits
	left := place.x - cellColumnUnits
	if p.aligns[i] == scene.AlignEnd {
		left = place.x + place.w + cellColumnUnits - width
	}
	return rect{x: left, y: place.y, w: width, h: place.h}
}

func (r rect) meets(o rect) bool {
	return max(r.x, o.x) < min(r.x+r.w, o.x+o.w) && max(r.y, o.y) < min(r.y+r.h, o.y+o.h)
}

func (p *sankeyPlan) labelRect(node rect, text sankeyText) (rect, scene.Align) {
	centre := geom.FloorDiv(2*node.y+node.h, 2)
	y := Clamp(centre-geom.FloorDiv(text.h, 2), 0, max(p.c.height-text.h, 0))
	if 2*node.x < p.c.width {
		return rect{x: node.x + node.w + p.c.labelGap, y: y, w: text.w, h: text.h}, scene.AlignStart
	}
	return rect{x: max(node.x-p.c.labelGap-text.w, 0), y: y, w: text.w, h: text.h}, scene.AlignEnd
}
