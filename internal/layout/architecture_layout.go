package layout

import (
	"errors"
	"maps"
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/grid"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var errArchDomain = errors.New("architecture layout: invalid model")

type archConstants struct {
	params   grid.ArchParams
	border   int32
	corner   int32
	junction int32
}

type archPlanner struct {
	in         Input
	profile    scene.Profile
	c          archConstants
	groupAt    []int
	nodeAt     []int
	groupIndex map[string]int
	nodeIndex  map[string]int
	specs      []archShapeSpec
	groupSpecs []archShapeSpec
	titles     [][]measure.StyledLine
	labels     [][]measure.StyledLine
	iconTexts  [][]measure.StyledLine
	edgeLabels [][]measure.StyledLine
	input      grid.ArchInput
	result     grid.ArchLayout
	dump       scene.Dump
}

func layoutArchitecture(in Input) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newArchPlanner(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	if p.result, err = grid.Architecture(p.input, p.c.params); err != nil {
		return scene.Scene{}, nil, err
	}
	if err = p.fill(); err != nil {
		return scene.Scene{}, nil, err
	}
	var ds []diag.Diagnostic
	if p.result.Budget {
		ds = append(ds, diag.Diagnostic{Code: "layout/budget-exhausted", Severity: diag.SeverityInfo, Message: "layout stopped at its iteration cap"})
	}
	return scene.Scene{Dump: p.dump, Groups: p.sceneGroups()}, ds, nil
}

func loadArchConstants(profile scene.Profile, config []scene.Config) (archConstants, error) {
	var c archConstants
	missing := false
	get := func(name string) int32 {
		value, ok := layoutConstant(profile, name)
		missing = missing || !ok
		return value
	}
	p := &c.params
	p.PitchX, p.PitchY, p.LabelWrap = get("architecture.pitch_x"), get("architecture.pitch_y"), get("architecture.label_wrap")
	p.IconW, p.IconH = get("architecture.icon_width"), get("architecture.icon_height")
	p.Padding, p.Badge, p.LineHeight = get("architecture.padding"), get("architecture.badge"), get("line_h")
	p.Inset, p.LabelGap, p.Thickness = get("architecture.title_inset"), get("architecture.label_gap"), get("architecture.line_thickness")
	p.Margin, p.Fuel, p.RingCap = get("canvas_margin"), get("architecture.bfs_cap"), get("architecture.ring_cap")
	c.junction, c.border, c.corner = get("architecture.junction_size"), get("node_border"), get("corner_radius")
	p.Gutter = archGutter(profile)
	if missing {
		return c, errArchDomain
	}
	for _, entry := range config {
		value, err := strconv.ParseInt(entry.Value, 10, 32)
		if err != nil || value < 0 {
			continue
		}
		c.configure(profile, entry.Key, int32(value))
	}
	return c, nil
}

func archGutter(profile scene.Profile) int32 {
	if profile == scene.ProfileCell {
		return 1
	}
	return 0
}

func (c *archConstants) configure(profile scene.Profile, key string, px int32) {
	cell := profile == scene.ProfileCell
	switch {
	case key == "padding" && cell:
		c.params.Padding = int32(geom.FloorDiv(2*int64(px)+20, 40))
	case key == "padding":
		c.params.Padding = px * 64
	case key == "iconSize" && px > 0 && cell:
		c.params.IconW = max(1, int32(geom.FloorDiv(14*int64(px)+80, 160)))
		c.params.IconH = max(1, int32(geom.FloorDiv(6*int64(px)+80, 160)))
	case key == "iconSize" && px > 0:
		c.params.IconW, c.params.IconH = px*64, px*64
	}
}

func archLimits(in Input) error {
	limits := resolveOptions(in.Options).Limits
	var bytes int64
	for _, box := range in.Boxes {
		bytes += int64(len(box.Text))
	}
	for _, label := range in.Labels {
		bytes += int64(len(label.Text))
	}
	for _, c := range []struct {
		resource      string
		limit, actual int64
	}{{"nodes", int64(limits.MaxNodes), int64(len(in.Boxes))}, {"edges", int64(limits.MaxEdges), int64(len(in.Routes))}, {"text bytes", int64(limits.MaxTextBytes), bytes}} {
		if c.actual > c.limit {
			return &layered.LimitError{Resource: c.resource, Limit: c.limit, Actual: c.actual}
		}
	}
	return nil
}

func newArchPlanner(in Input) (*archPlanner, error) {
	if err := archLimits(in); err != nil {
		return nil, err
	}
	p := &archPlanner{in: in, profile: in.Profile, groupIndex: map[string]int{}, nodeIndex: map[string]int{}}
	var err error
	if p.c, err = loadArchConstants(in.Profile, in.Options.Config); err != nil {
		return nil, err
	}
	for i, box := range in.Boxes {
		spec := parseArchShape(box.Shape)
		if box.Role == scene.RoleGroup {
			p.groupIndex[box.ID] = len(p.groupAt)
			p.groupAt = append(p.groupAt, i)
			p.groupSpecs = append(p.groupSpecs, spec)
			continue
		}
		p.nodeIndex[box.ID] = len(p.nodeAt)
		p.nodeAt = append(p.nodeAt, i)
		p.specs = append(p.specs, spec)
	}
	if err = p.measure(); err != nil {
		return nil, err
	}
	return p, p.gridInput()
}

func (p *archPlanner) lines(text string, wrap int32) ([]measure.StyledLine, error) {
	if text == "" {
		return nil, nil
	}
	lines, err := measure.StyledLines(text, wrap, sequenceMetric(p.profile, measure.RoleLabel).WithFontFamily(p.in.Options.FontFamily))
	if err != nil {
		return nil, geom.ErrOverflow
	}
	return lines, nil
}

func (p *archPlanner) extent(lines []measure.StyledLine) geom.Size {
	var width int64
	for _, line := range lines {
		width = max(width, int64(line.Width))
	}
	height := int64(len(lines)) * int64(p.c.params.LineHeight)
	limit := geom.CoordLimit
	return geom.Size{W: int32(min(width, limit)), H: int32(min(height, limit))}
}

func (p *archPlanner) measure() error {
	for _, i := range p.groupAt {
		lines, err := p.lines(p.in.Boxes[i].Text, geom.I32Max)
		if err != nil {
			return err
		}
		p.titles = append(p.titles, lines)
	}
	params := p.c.params
	for k, i := range p.nodeAt {
		label, err := p.lines(p.in.Boxes[i].Text, params.LabelWrap)
		if err != nil {
			return err
		}
		inner, err := p.lines(p.specs[k].IconText, max(1, params.IconW-2*params.Inset))
		if err != nil {
			return err
		}
		p.labels = append(p.labels, label)
		p.iconTexts = append(p.iconTexts, inner)
	}
	for _, route := range p.in.Routes {
		lines := []measure.StyledLine(nil)
		if j := p.labelOf(route.ID); j >= 0 {
			var err error
			if lines, err = p.lines(p.in.Labels[j].Text, geom.I32Max); err != nil {
				return err
			}
		}
		p.edgeLabels = append(p.edgeLabels, lines)
	}
	return nil
}

func (p *archPlanner) labelOf(owner string) int {
	return slices.IndexFunc(p.in.Labels, func(l Label) bool { return l.Owner == owner })
}

func (p *archPlanner) groupOf(id string) (int, bool) {
	if id == "" {
		return -1, true
	}
	index, ok := p.groupIndex[id]
	return index, ok
}

func (p *archPlanner) gridInput() error {
	params := p.c.params
	for k, i := range p.groupAt {
		parent, ok := p.groupOf(p.in.Boxes[i].Parent)
		if !ok {
			return errArchDomain
		}
		p.input.Groups = append(p.input.Groups, grid.ArchGroup{Parent: parent, Title: p.extent(p.titles[k]), Icon: p.groupSpecs[k].Icon != ""})
	}
	for k, i := range p.nodeAt {
		parent, ok := p.groupOf(p.in.Boxes[i].Parent)
		if !ok {
			return errArchDomain
		}
		node := grid.ArchNode{Parent: parent, Icon: geom.Size{W: params.IconW, H: params.IconH}, Label: p.extent(p.labels[k])}
		if p.specs[k].Kind == "junction" {
			node.Junction, node.Icon = true, geom.Size{W: p.c.junction, H: p.c.junction}
		}
		p.input.Nodes = append(p.input.Nodes, node)
	}
	for k, route := range p.in.Routes {
		from, okFrom := p.nodeIndex[route.From]
		to, okTo := p.nodeIndex[route.To]
		if !okFrom || !okTo {
			return errArchDomain
		}
		p.input.Edges = append(p.input.Edges, grid.ArchEdge{From: from, To: to, FromSide: route.FromSide, ToSide: route.ToSide, Label: p.extent(p.edgeLabels[k])})
	}
	p.input.Aligns = p.alignSets()
	return nil
}

type alignMember struct{ pos, node int }

func (p *archPlanner) alignSets() []grid.ArchAlign {
	members := map[int][]alignMember{}
	columns := map[int]bool{}
	for node, spec := range p.specs {
		for _, a := range spec.Aligns {
			members[a.Set] = append(members[a.Set], alignMember{a.Pos, node})
			columns[a.Set] = a.Column
		}
	}
	var out []grid.ArchAlign
	for _, set := range slices.Sorted(maps.Keys(members)) {
		list := members[set]
		slices.SortFunc(list, func(a, b alignMember) int {
			if a.pos != b.pos {
				return a.pos - b.pos
			}
			return a.node - b.node
		})
		entry := grid.ArchAlign{Column: columns[set]}
		for _, m := range list {
			entry.Members = append(entry.Members, m.node)
		}
		out = append(out, entry)
	}
	return out
}

func (p *archPlanner) routeOf(id string) int {
	return slices.IndexFunc(p.in.Routes, func(r Route) bool { return r.ID == id })
}

func (p *archPlanner) fill() error {
	options := resolveOptions(p.in.Options)
	options.Profile, options.Direction = p.profile, p.in.Direction
	d := scene.Dump{Kind: architectureKind, Options: options, Canvas: p.result.Canvas}
	groups, nodes := 0, 0
	for _, box := range p.in.Boxes {
		entry := scene.Box{ID: box.ID, Role: box.Role, Parent: box.Parent, Exclusive: box.Exclusive}
		if box.Role == scene.RoleGroup {
			entry.Rect = p.result.Frames[groups]
			groups++
		} else {
			entry.Rect = p.result.Boxes[nodes]
			nodes++
		}
		d.Boxes = append(d.Boxes, entry)
	}
	for i, route := range p.in.Routes {
		d.Routes = append(d.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: true, Points: p.result.Routes[i], MarkerStart: route.MarkerStart, MarkerEnd: route.MarkerEnd, Stroke: route.Line})
	}
	for _, label := range p.in.Labels {
		k := p.routeOf(label.Owner)
		if k < 0 {
			return errArchDomain
		}
		entry := scene.Label{ID: label.ID, Owner: label.Owner, Text: label.Text, Rect: p.result.EdgeLabels[k]}
		for _, line := range p.edgeLabels[k] {
			entry.Lines = append(entry.Lines, line.Text)
		}
		d.Labels = append(d.Labels, entry)
	}
	p.dump = d
	return nil
}
