package layout

import (
	"errors"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/layout/tree"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	ishikawamodel "github.com/gosuda/elegant-mermaid/internal/model/ishikawa"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	ishikawaparser "github.com/gosuda/elegant-mermaid/internal/syntax/ishikawa"
)

const (
	ishikawaKind   = "ishikawa"
	ishikawaEffect = "effect"
	ishikawaCause  = "cause:"
	ishikawaAnchor = "anchor"
	ishikawaMarker = "point"
)

var errIshikawaInput = errors.New("ishikawa layout: invalid input")

func (d *Diagram) resolveIshikawa() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := ishikawaparser.Parse(d.Source, d.Preprocessing.Removed)
	d.ishikawa, resolved = ishikawamodel.Resolve(d.Source, ast)
	return parsed, resolved
}

func (d *Diagram) ishikawaInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromIshikawa(d.ishikawa, profile, options)
	return input, diagnostics, nil
}

func ishikawaBoxID(index int) string { return "n" + strconv.Itoa(index) }

func ishikawaAnchorID(index int) string { return "a" + strconv.Itoa(index) }

func ishikawaRouteID(index int) string { return "e" + strconv.Itoa(index) }

func FromIshikawa(m *ishikawamodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	options.Profile = profile
	in := Input{Kind: ishikawaKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	for _, node := range m.Nodes {
		id := ishikawaBoxID(node.Index)
		shape := ishikawaEffect
		if node.Index > 0 {
			shape = ishikawaCause + strconv.Itoa(node.Depth)
		}
		in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: shape, Exclusive: true})
		if node.Label != id {
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: node.Label})
		}
	}
	if len(m.Nodes) > 1 {
		in.addIshikawaRoutes(m)
	}
	return in, nil
}

func (in *Input) addIshikawaRoutes(m *ishikawamodel.Model) {
	for _, node := range m.Nodes {
		in.Boxes = append(in.Boxes, Box{ID: ishikawaAnchorID(node.Index), Role: scene.RoleNode, Shape: ishikawaAnchor})
		route := Route{ID: ishikawaRouteID(node.Index), From: ishikawaAnchorID(node.Index), To: ishikawaBoxID(node.Index), MarkerEnd: "none", Line: "normal"}
		if node.Index == 0 {
			route.Orthogonal = true
		} else {
			route.Orthogonal = node.Depth%2 == 0
			route.MarkerStart = ishikawaMarker
		}
		in.Routes = append(in.Routes, route)
	}
}

type ishikawaConstants struct {
	padX, padY, border, minW, minH int32
	lineHeight, margin, corner     int32
	params                         tree.IshikawaParams
}

func loadIshikawaConstants(profile scene.Profile) (ishikawaConstants, error) {
	var c ishikawaConstants
	required := []struct {
		name string
		into *int32
	}{
		{"node_pad_x", &c.padX}, {"node_pad_y", &c.padY}, {"node_border", &c.border}, {"node_min_w", &c.minW},
		{"node_min_h", &c.minH}, {"line_h", &c.lineHeight}, {"canvas_margin", &c.margin}, {"corner_radius", &c.corner},
		{"ishikawa.spine_base_length", &c.params.SpineBase}, {"ishikawa.rib_min_length", &c.params.RibMin},
		{"ishikawa.rib_pool", &c.params.RibPool}, {"ishikawa.cause_min_spacing", &c.params.MinSpacing},
		{"ishikawa.bone_stub", &c.params.BoneStub}, {"ishikawa.bone_base", &c.params.BoneBase},
		{"ishikawa.bone_per_child", &c.params.BonePerChild}, {"ishikawa.spine_inset", &c.params.Inset},
		{"ishikawa.rib_cos_q15", &c.params.Cos}, {"ishikawa.rib_sin_q15", &c.params.Sin},
	}
	for _, row := range required {
		value, ok := layoutConstant(profile, row.name)
		if !ok {
			return ishikawaConstants{}, errIshikawaInput
		}
		*row.into = value
	}
	return c, nil
}

type ishikawaPlan struct {
	in    Input
	c     ishikawaConstants
	count int
	lines [][]measure.StyledLine
	nodes []tree.Node
	depth []int
}

func newIshikawaPlan(in Input) (*ishikawaPlan, error) {
	if err := ishikawaLimits(in); err != nil {
		return nil, err
	}
	c, err := loadIshikawaConstants(in.Profile)
	if err != nil {
		return nil, err
	}
	p := &ishikawaPlan{in: in, c: c}
	if err := p.readDepths(); err != nil {
		return nil, err
	}
	return p, p.measure()
}

func ishikawaLimits(in Input) error {
	if nodes := int64(len(in.Boxes)); nodes > int64(in.Options.Limits.MaxNodes) {
		return &layered.LimitError{Resource: "nodes", Limit: int64(in.Options.Limits.MaxNodes), Actual: nodes}
	}
	if edges := int64(len(in.Routes)); edges > int64(in.Options.Limits.MaxEdges) {
		return &layered.LimitError{Resource: "edges", Limit: int64(in.Options.Limits.MaxEdges), Actual: edges}
	}
	var bytes int64
	for _, label := range in.Labels {
		bytes += int64(len(label.Text))
	}
	if bytes > int64(in.Options.Limits.MaxTextBytes) {
		return &layered.LimitError{Resource: "text bytes", Limit: int64(in.Options.Limits.MaxTextBytes), Actual: bytes}
	}
	return nil
}

func ishikawaCauseDepth(shape string) (int, bool) {
	text, ok := strings.CutPrefix(shape, ishikawaCause)
	depth, err := strconv.Atoi(text)
	return depth, ok && err == nil && depth >= 1 && depth <= tree.IshikawaMaxDepth
}

func (p *ishikawaPlan) readDepths() error {
	boxes := p.in.Boxes
	if len(boxes) > 0 && (boxes[0].Shape == ishikawaEffect || boxes[0].Shape == "") {
		p.depth, p.count = []int{0}, 1
	}
	for p.count > 0 && p.count < len(boxes) {
		depth, ok := ishikawaCauseDepth(boxes[p.count].Shape)
		if !ok {
			break
		}
		p.depth = append(p.depth, depth)
		p.count++
	}
	for _, box := range boxes[p.count:] {
		if box.Shape != ishikawaAnchor {
			return errIshikawaInput
		}
	}
	return nil
}

func (p *ishikawaPlan) labelText(box Box) string {
	for _, label := range p.in.Labels {
		if label.Owner == box.ID {
			return label.Text
		}
	}
	return box.ID
}

func (p *ishikawaPlan) bordered(index int) bool { return p.depth[index] <= 1 }

func (p *ishikawaPlan) measure() error {
	metric := measure.CellMetric()
	maxWidth := p.in.Options.MaxWidth
	if p.in.Profile == scene.ProfileVector {
		metric, maxWidth = measure.ForRole(measure.RoleLabel), 0
	}
	metric = metric.WithFontFamily(p.in.Options.FontFamily)
	wrap := measure.WrapTarget(metric.Profile, 0, maxWidth)
	parents, err := p.parents()
	if err != nil {
		return err
	}
	for i := range p.count {
		lines, err := measure.StyledLines(p.labelText(p.in.Boxes[i]), wrap, metric)
		if err != nil {
			return geom.ErrOverflow
		}
		w, h, err := p.boxSize(i, lines)
		if err != nil {
			return err
		}
		p.lines = append(p.lines, lines)
		p.nodes = append(p.nodes, tree.Node{Parent: parents[i], Width: w, Height: h})
	}
	return nil
}

func (p *ishikawaPlan) parents() ([]int, error) {
	parents := make([]int, p.count)
	var path []int
	for i := range p.count {
		d := p.depth[i]
		if d > len(path) {
			return nil, errIshikawaInput
		}
		path = append(path[:d], i)
		parents[i] = tree.NoParent
		if d > 0 {
			parents[i] = path[d-1]
		}
	}
	return parents, nil
}

func (p *ishikawaPlan) boxSize(index int, lines []measure.StyledLine) (int32, int32, error) {
	w := int64(widestLine(lines)) + 2*int64(p.c.padX)
	h := int64(max(len(lines), 1)) * int64(p.c.lineHeight)
	if p.bordered(index) {
		w = max(w+2*int64(p.c.border), int64(p.c.minW))
		h = max(h+2*int64(p.c.padY)+2*int64(p.c.border), int64(p.c.minH))
	}
	if w > geom.CoordLimit || h > geom.CoordLimit {
		return 0, 0, geom.ErrOverflow
	}
	return int32(max(w, 1)), int32(max(h, 1)), nil
}

func layoutIshikawa(in Input) (scene.Scene, []diag.Diagnostic, error) {
	in.Options = resolveOptions(in.Options)
	p, err := newIshikawaPlan(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	placed, err := tree.Ishikawa(p.nodes, p.c.params)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	canvas, err := tree.Normalize(&placed, p.c.margin)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump, err := p.dump(placed, canvas)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	return scene.Scene{Dump: dump, Groups: p.groups(dump)}, nil, nil
}

func (p *ishikawaPlan) dump(placed tree.Layout, canvas geom.Size) (scene.Dump, error) {
	options := p.in.Options
	options.Profile, options.Direction = p.in.Profile, p.in.Direction
	d := scene.Dump{Kind: ishikawaKind, Options: options, Canvas: canvas}
	for i, box := range p.in.Boxes {
		rect := geom.Rect{}
		if i < p.count {
			rect = placed.Boxes[i]
		}
		d.Boxes = append(d.Boxes, scene.Box{ID: box.ID, Role: box.Role, Rect: rect, Exclusive: box.Exclusive})
	}
	anchor := p.count
	for _, route := range p.in.Routes {
		k := p.nodeOf(route.To)
		if k < 0 || anchor >= len(d.Boxes) || d.Boxes[anchor].ID != route.From || len(placed.Routes[k]) < 2 {
			return scene.Dump{}, errIshikawaInput
		}
		points := placed.Routes[k]
		d.Boxes[anchor].Rect = geom.Rect{X: points[0].X, Y: points[0].Y}
		anchor++
		d.Routes = append(d.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: route.Orthogonal, Points: points})
	}
	return d, nil
}

func (p *ishikawaPlan) nodeOf(id string) int {
	for i := range p.count {
		if p.in.Boxes[i].ID == id {
			return i
		}
	}
	return -1
}
