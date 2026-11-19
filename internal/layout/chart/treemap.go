package chart

import (
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	TreemapRootID = "root"
	treemapNodeID = "n"
)

type treemapLeafConsts struct {
	labelSize, valueSize, labelMin, valueMin int64
	pad, minDisplay, spacing                 int64
}

type treemapConsts struct {
	width, height, titleBand              int64
	header, headerBorder                  int64
	padX, padY, innerX, innerY            int64
	rho, valueBits, fuel                  int64
	labelInset, valueInset, gap, labelMin int64
	headerLabelSize, headerValueSize      int64
	dense, valuePercent                   int64
	sparse, thick                         treemapLeafConsts
}

func loadTreemapLeaf(profile scene.Profile, suffix string) (treemapLeafConsts, error) {
	var c treemapLeafConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"leaf_label_size", &c.labelSize}, {"leaf_value_size", &c.valueSize}, {"leaf_label_min", &c.labelMin},
		{"leaf_value_min", &c.valueMin}, {"leaf_pad", &c.pad}, {"leaf_min_display", &c.minDisplay}, {"leaf_spacing", &c.spacing},
	} {
		value, err := constant(profile, "treemap."+row.name+suffix)
		if err != nil {
			return treemapLeafConsts{}, err
		}
		*row.into = value
	}
	return c, nil
}

func loadTreemapConsts(profile scene.Profile, m *chartmodel.Chart) (treemapConsts, error) {
	var c treemapConsts
	for _, row := range []struct {
		name string
		into *int64
	}{
		{"width", &c.width}, {"height", &c.height}, {"title_band", &c.titleBand}, {"section_header", &c.header},
		{"header_border", &c.headerBorder}, {"section_padding_x", &c.padX}, {"section_padding_y", &c.padY},
		{"inner_padding_x", &c.innerX}, {"inner_padding_y", &c.innerY}, {"rho_q30", &c.rho}, {"value_bits", &c.valueBits},
		{"squarify_cap", &c.fuel}, {"header_label_inset", &c.labelInset}, {"header_value_inset", &c.valueInset},
		{"header_gap", &c.gap}, {"header_label_min", &c.labelMin}, {"header_label_size", &c.headerLabelSize},
		{"header_value_size", &c.headerValueSize}, {"dense_leaves", &c.dense}, {"value_scale_percent", &c.valuePercent},
	} {
		value, err := constant(profile, "treemap."+row.name)
		if err != nil {
			return treemapConsts{}, err
		}
		*row.into = value
	}
	var err error
	if c.sparse, err = loadTreemapLeaf(profile, ""); err != nil {
		return treemapConsts{}, err
	}
	if c.thick, err = loadTreemapLeaf(profile, "_dense"); err != nil {
		return treemapConsts{}, err
	}
	c.applyConfig(profile, m)
	return c, nil
}

func treemapSide(profile scene.Profile, px, cellPx int64) int64 {
	if profile == scene.ProfileCell {
		return (px + cellPx - 1) / cellPx
	}
	return px * 64
}

func (c *treemapConsts) applyConfig(profile scene.Profile, m *chartmodel.Chart) {
	if n, ok := m.Integer("nodeWidth"); ok {
		c.width = treemapSide(profile, n*10, 8)
	}
	if n, ok := m.Integer("nodeHeight"); ok {
		c.height = treemapSide(profile, n*10, 16)
	}
	if n, ok := m.Integer("padding"); ok {
		c.innerX, c.innerY = treemapSide(profile, n, 8), treemapSide(profile, n, 16)
	}
}

type treemapNode struct {
	name, valueText       string
	parent                int
	kids, order           []int
	raw, norm             int64
	index                 int
	series                int
	nameLabel, valueLabel int
	cell, rect            tile
}

func flattenTreemap(t *chartmodel.Treemap) []treemapNode {
	nodes := []treemapNode{{parent: -1}}
	type pending struct {
		node   *chartmodel.TreemapNode
		parent int
	}
	var stack []pending
	push := func(children []*chartmodel.TreemapNode, parent int) {
		for i := len(children) - 1; i >= 0; i-- {
			stack = append(stack, pending{children[i], parent})
		}
	}
	push(t.Roots, 0)
	for len(stack) > 0 {
		next := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		at := len(nodes)
		nodes = append(nodes, treemapNode{
			name: next.node.Name, valueText: next.node.ValueText, parent: next.parent,
			raw: int64(next.node.Value), index: next.node.Index,
		})
		nodes[next.parent].kids = append(nodes[next.parent].kids, at)
		push(next.node.Children, at)
	}
	return nodes
}

type treemapPlan struct {
	c       treemapConsts
	profile scene.Profile
	cell    bool
	title   string
	nodes   []treemapNode
	leaves  int
	canvasW int64
	canvasH int64
	capped  bool
	labels  []treemapLabel
}

func newTreemapPlan(m *chartmodel.Chart, o scene.Options) (*treemapPlan, error) {
	c, err := loadTreemapConsts(o.Profile, m)
	if err != nil {
		return nil, err
	}
	p := &treemapPlan{c: c, profile: o.Profile, cell: o.Profile == scene.ProfileCell, title: m.Title, nodes: flattenTreemap(m.Treemap)}
	if err = p.aggregate(); err != nil {
		return nil, err
	}
	for i := range p.nodes {
		if i > 0 && len(p.nodes[i].kids) == 0 {
			p.leaves++
		}
	}
	p.sortChildren()
	p.assignSeries()
	band := int64(0)
	if m.Title != "" {
		band = c.titleBand
	}
	p.canvasW, p.canvasH = c.width, band+c.height
	p.nodes[0].rect = tile{0, band, c.width, band + c.height}
	p.labels = p.labelSpecs()
	return p, nil
}

const treemapRawCap = int64(1) << 43

func normalizeTreemap(raw []int64, valueBits int64) ([]int64, error) {
	var total int64
	for _, v := range raw {
		switch {
		case v < 0:
			return nil, errDomain
		case v > treemapRawCap:
			return nil, ErrOverflow
		case total > math.MaxInt64-v:
			return nil, ErrOverflow
		}
		total += v
	}
	out := slices.Clone(raw)
	budget := int64(1) << valueBits
	if total <= budget {
		return out, nil
	}
	for i, v := range raw {
		out[i] = int64(quotient(mulU128(uint64(v), uint64(budget)), u128{lo: uint64(total)}).lo)
	}
	return out, nil
}

// TreemapNormalize scales leaf values so that their total stays within the squarify budget.
func TreemapNormalize(raw []int64) ([]int64, error) {
	bits, err := constant(scene.ProfileVector, "treemap.value_bits")
	if err != nil {
		return nil, err
	}
	return normalizeTreemap(raw, bits)
}

func (p *treemapPlan) aggregate() error {
	var leaves []int
	var raw []int64
	for i := 1; i < len(p.nodes); i++ {
		if len(p.nodes[i].kids) == 0 {
			leaves = append(leaves, i)
			raw = append(raw, p.nodes[i].raw)
		}
	}
	norm, err := normalizeTreemap(raw, p.c.valueBits)
	if err != nil {
		return err
	}
	for k, i := range leaves {
		p.nodes[i].norm = norm[k]
	}
	for i := len(p.nodes) - 1; i > 0; i-- {
		p.nodes[p.nodes[i].parent].norm += p.nodes[i].norm
	}
	return nil
}

func (p *treemapPlan) sortChildren() {
	for i := range p.nodes {
		n := &p.nodes[i]
		n.order = slices.Clone(n.kids)
		slices.SortFunc(n.order, func(a, b int) int {
			switch {
			case p.nodes[a].norm != p.nodes[b].norm:
				if p.nodes[a].norm > p.nodes[b].norm {
					return -1
				}
				return 1
			case a < b:
				return -1
			case a > b:
				return 1
			}
			return 0
		})
	}
}

func (p *treemapPlan) assignSeries() {
	for k, id := range p.nodes[0].kids {
		p.nodes[id].series = k
	}
	for i := 1; i < len(p.nodes); i++ {
		if parent := p.nodes[i].parent; parent > 0 {
			p.nodes[i].series = p.nodes[parent].series
		}
	}
}

func containedSpan(lo, hi, parentLo, parentHi int64) (int64, int64) {
	if hi < lo {
		mid := geom.FloorDiv(lo+hi, 2)
		lo, hi = mid, mid
	}
	return max(parentLo, min(parentHi, lo)), max(parentLo, min(parentHi, hi))
}

func (p *treemapPlan) childArea(r tile) tile {
	hx, hy := geom.FloorDiv(p.c.innerX, 2), geom.FloorDiv(p.c.innerY, 2)
	x0, x1 := containedSpan(r.x0+p.c.padX-hx, r.x1-(p.c.padX-hx), r.x0, r.x1)
	y0, y1 := containedSpan(r.y0+p.c.header+p.c.padY-hy, r.y1-(p.c.padY-hy), r.y0, r.y1)
	return tile{x0, y0, x1, y1}
}

func (p *treemapPlan) tileAll() error {
	hx, hy := geom.FloorDiv(p.c.innerX, 2), geom.FloorDiv(p.c.innerY, 2)
	for i := range p.nodes {
		n := &p.nodes[i]
		if len(n.order) == 0 {
			continue
		}
		values := make([]int64, len(n.order))
		for k, id := range n.order {
			values[k] = p.nodes[id].norm
		}
		cells, capped, err := squarify(values, p.childArea(n.rect), uint64(p.c.rho), int(p.c.fuel))
		if err != nil {
			return err
		}
		p.capped = p.capped || capped
		for k, id := range n.order {
			child := &p.nodes[id]
			child.cell = cells[k]
			x0, x1 := containedSpan(cells[k].x0+hx, cells[k].x1-hx, cells[k].x0, cells[k].x1)
			y0, y1 := containedSpan(cells[k].y0+hy, cells[k].y1-hy, cells[k].y0, cells[k].y1)
			child.rect = tile{x0, y0, x1, y1}
		}
	}
	return nil
}

func (t tile) rect() rect { return rect{t.x0, t.y0, t.x1 - t.x0, t.y1 - t.y0} }

func treemapBoxID(i int) string {
	if i == 0 {
		return TreemapRootID
	}
	return treemapNodeID + itoa(i-1)
}

func (p *treemapPlan) role(i int) scene.BoxRole {
	if i == 0 || len(p.nodes[i].kids) > 0 {
		return scene.RoleGroup
	}
	return scene.RoleNode
}

func (p *treemapPlan) dumpBoxes() ([]scene.Box, error) {
	boxes := make([]scene.Box, len(p.nodes))
	for i := range p.nodes {
		parent := ""
		if i > 0 {
			parent = treemapBoxID(p.nodes[i].parent)
		}
		g, err := p.nodes[i].rect.rect().geom()
		if err != nil {
			return nil, err
		}
		boxes[i] = scene.Box{ID: treemapBoxID(i), Role: p.role(i), Rect: g, Parent: parent}
	}
	return boxes, nil
}

func layoutTreemap(m *chartmodel.Chart, o scene.Options) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newTreemapPlan(m, o)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.tileAll(); err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.placeAll(); err != nil {
		return scene.Scene{}, nil, err
	}
	w, err := i32(p.canvasW)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	h, err := i32(p.canvasH)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	boxes, err := p.dumpBoxes()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := scene.Dump{Stage: scene.StageLayout, Kind: string(m.Kind), Options: o, Canvas: geom.Size{W: w, H: h}, Boxes: boxes, Labels: p.dumpLabels()}
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

func treemapSkeleton(m *chartmodel.Chart) (Skeleton, error) {
	p, err := newTreemapPlan(m, scene.Options{})
	if err != nil {
		return Skeleton{}, err
	}
	boxes := make([]scene.Box, len(p.nodes))
	for i := range p.nodes {
		parent := ""
		if i > 0 {
			parent = treemapBoxID(p.nodes[i].parent)
		}
		boxes[i] = scene.Box{ID: treemapBoxID(i), Role: p.role(i), Parent: parent}
	}
	return Skeleton{Boxes: boxes, Labels: p.dumpLabels()}, nil
}
