package layout

import (
	"errors"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/grid"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var errBlockDomain = errors.New("block layout: invalid model")

type blockPlanner struct {
	in         Input
	profile    scene.Profile
	padding    int32
	lineHeight int32
	corner     int32
	specs      []blockShapeSpec
	lines      [][]measure.StyledLine
	labelLines [][]measure.StyledLine
	index      map[string]int
	params     grid.Params
	dump       scene.Dump
}

func layoutBlock(in Input) (scene.Scene, []diag.Diagnostic, error) {
	p, err := newBlockPlanner(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	input, err := p.gridInput()
	if err != nil {
		return scene.Scene{}, nil, err
	}
	result, err := grid.Block(input, p.params)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	p.fill(result)
	return scene.Scene{Dump: p.dump, Groups: p.groups()}, nil, nil
}

func withBlockRoot(in Input) Input {
	if len(in.Boxes) > 0 && in.Boxes[0].Role == scene.RoleGroup && in.Boxes[0].Parent == "" && parseBlockShape(in.Boxes[0].Shape).Type == "composite" {
		return in
	}
	taken := make(map[string]struct{}, len(in.Boxes))
	for _, box := range in.Boxes {
		taken[box.ID] = struct{}{}
	}
	id := "root"
	for ordinal := 1; routeIDTaken(taken, id); ordinal++ {
		id = "root" + strconv.Itoa(ordinal)
	}
	in.Boxes = append([]Box{{ID: id, Role: scene.RoleGroup, Shape: "composite"}}, in.Boxes...)
	return in
}

func newBlockPlanner(in Input) (*blockPlanner, error) {
	in = withBlockRoot(in)
	p := &blockPlanner{in: in, profile: in.Profile, index: map[string]int{"": 0}}
	for i, box := range in.Boxes {
		p.index[box.ID] = i
		p.specs = append(p.specs, parseBlockShape(box.Shape))
	}
	if err := p.constants(); err != nil {
		return nil, err
	}
	if err := p.measure(); err != nil {
		return nil, err
	}
	return p, nil
}

func (p *blockPlanner) constants() error {
	padding, okPad := layoutConstant(p.profile, "block.padding")
	line, okLine := layoutConstant(p.profile, "line_h")
	bend, okBend := layoutConstant(p.profile, "block.bend_cost")
	thick, okThick := layoutConstant(p.profile, "block.line_thickness")
	corner, okCorner := layoutConstant(p.profile, "corner_radius")
	if !okPad || !okLine || !okBend || !okThick || !okCorner {
		return errBlockDomain
	}
	for _, c := range p.in.Options.Config {
		if value, err := strconv.ParseInt(c.Value, 10, 32); c.Key == "padding" && err == nil && value >= 0 {
			padding = p.scalePadding(int32(value))
		}
	}
	p.padding, p.lineHeight, p.corner = padding, line, corner
	p.params = grid.Params{Padding: padding, BendCost: bend, LineThickness: thick}
	return nil
}

func (p *blockPlanner) scalePadding(px int32) int32 {
	if p.profile == scene.ProfileCell {
		return max(1, (px+7)/8)
	}
	return px * 64
}

func (p *blockPlanner) measureText(text string) ([]measure.StyledLine, error) {
	lines, err := measure.StyledLines(text, geom.I32Max, sequenceMetric(p.profile, measure.RoleLabel).WithFontFamily(p.in.Options.FontFamily))
	if err != nil {
		return nil, geom.ErrOverflow
	}
	return lines, nil
}

func (p *blockPlanner) measure() error {
	for i, box := range p.in.Boxes {
		var lines []measure.StyledLine
		if box.Role == scene.RoleNode && p.specs[i].Type != "space" {
			var err error
			if lines, err = p.measureText(boxText(p.in, box)); err != nil {
				return err
			}
		}
		p.lines = append(p.lines, lines)
	}
	for _, label := range p.in.Labels {
		lines, err := p.measureText(label.Text)
		if err != nil {
			return err
		}
		p.labelLines = append(p.labelLines, lines)
	}
	return nil
}

func (p *blockPlanner) extent(lines []measure.StyledLine) geom.Size {
	var width int64
	for _, line := range lines {
		width = max(width, int64(line.Width))
	}
	height := int64(len(lines)) * int64(p.lineHeight)
	limit := int64(geom.CoordLimit)
	return geom.Size{W: int32(min(width, limit)), H: int32(min(height, limit))}
}

func (p *blockPlanner) gridInput() (grid.Input, error) {
	input := grid.Input{Columns: p.specs[0].Columns}
	for i := 1; i < len(p.in.Boxes); i++ {
		parent, ok := p.index[p.in.Boxes[i].Parent]
		if !ok {
			return grid.Input{}, errBlockDomain
		}
		input.Boxes = append(input.Boxes, p.gridBox(i, parent-1))
	}
	for _, route := range p.in.Routes {
		from, okFrom := p.index[route.From]
		to, okTo := p.index[route.To]
		if !okFrom || !okTo || from == 0 || to == 0 {
			return grid.Input{}, errBlockDomain
		}
		input.Edges = append(input.Edges, p.gridEdge(route, from-1, to-1))
	}
	return input, nil
}

func (p *blockPlanner) gridBox(i, parent int) grid.Box {
	entry := grid.Box{Parent: parent, Kind: grid.KindLeaf, Span: p.specs[i].Span, Columns: p.specs[i].Columns}
	switch {
	case p.in.Boxes[i].Role == scene.RoleGroup:
		entry.Kind = grid.KindComposite
	case p.specs[i].Type == "space":
		entry.Kind = grid.KindSpace
	default:
		text := p.extent(p.lines[i])
		entry.Size = geom.Size{W: addClamped(text.W, 2*p.padding), H: addClamped(text.H, 2*p.padding)}
	}
	return entry
}

func (p *blockPlanner) gridEdge(route Route, from, to int) grid.Edge {
	edge := grid.Edge{From: from, To: to}
	if j := p.labelOf(route.ID); j >= 0 {
		edge.Label = p.extent(p.labelLines[j])
	}
	return edge
}

func addClamped(a, b int32) int32 {
	return int32(min(int64(a)+int64(b), int64(geom.CoordLimit)))
}

func (p *blockPlanner) labelOf(owner string) int {
	for j, label := range p.in.Labels {
		if label.Owner == owner {
			return j
		}
	}
	return -1
}

func (p *blockPlanner) routeOf(id string) int {
	for i, route := range p.in.Routes {
		if route.ID == id {
			return i
		}
	}
	return -1
}

func (p *blockPlanner) fill(result grid.Layout) {
	options := resolveOptions(p.in.Options)
	options.Profile, options.Direction = p.profile, p.in.Direction
	d := scene.Dump{Kind: blockKind, Options: options, Canvas: result.Canvas}
	last := len(result.Rects) - 1
	rects := append([]geom.Rect{result.Rects[last]}, result.Rects[:last]...)
	for i, box := range p.in.Boxes {
		d.Boxes = append(d.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: rects[i], Parent: box.Parent, Exclusive: box.Exclusive})
	}
	for i, route := range p.in.Routes {
		d.Routes = append(d.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: true, Points: result.Routes[i], MarkerStart: route.MarkerStart, MarkerEnd: route.MarkerEnd, Stroke: route.Line})
	}
	for j, label := range p.in.Labels {
		entry := scene.Label{ID: label.ID, Owner: label.Owner, Text: label.Text, Rect: result.Labels[p.routeOf(label.Owner)]}
		for _, line := range p.labelLines[j] {
			entry.Lines = append(entry.Lines, line.Text)
		}
		d.Labels = append(d.Labels, entry)
	}
	p.dump = d
}
