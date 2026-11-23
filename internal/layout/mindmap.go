package layout

import (
	"errors"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/layout/tree"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	mindmapmodel "github.com/gosuda/elegant-mermaid/internal/model/mindmap"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	mindmapKind       = "mindmap"
	mindmapPaddingKey = "padding"
	mindmapMaxWidth   = "maxNodeWidth"
	pixelUnits        = 64
)

var errMindmapDomain = errors.New("mindmap layout: invalid geometry")

func FromMindmap(m *mindmapmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	if m.Config.MaxNodeWidthSet {
		options.Config = append(options.Config, scene.Config{Key: mindmapMaxWidth, Value: strconv.FormatInt(m.Config.MaxNodeWidth, 10)})
	}
	if m.Config.PaddingSet {
		options.Config = append(options.Config, scene.Config{Key: mindmapPaddingKey, Value: strconv.FormatInt(m.Config.Padding, 10)})
	}
	options.Profile = profile
	in := Input{Kind: mindmapKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	for _, node := range m.Nodes {
		id := mindmapBoxID(node.Index)
		in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: node.Shape.String(), Exclusive: true})
		if node.Label != id {
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleLabel, Text: node.Label})
		}
		if node.Parent != mindmapmodel.NoParent {
			in.Routes = append(in.Routes, Route{ID: "e" + strconv.Itoa(len(in.Routes)), From: mindmapBoxID(node.Parent), To: id, Orthogonal: true, Line: "normal"})
		}
	}
	return in, nil
}

func mindmapBoxID(index int) string { return "n" + strconv.Itoa(index) }

type mindmapConstants struct {
	padding, maxWidth, levelGap, siblingGap int32
	lineHeight, margin, corner              int32
}

func loadMindmapConstants(in Input) (mindmapConstants, error) {
	var c mindmapConstants
	required := []struct {
		name string
		into *int32
	}{
		{"mindmap.padding", &c.padding}, {"mindmap.max_node_width", &c.maxWidth}, {"mindmap.level_gap", &c.levelGap},
		{"mindmap.sibling_gap", &c.siblingGap}, {"line_h", &c.lineHeight}, {"canvas_margin", &c.margin}, {"corner_radius", &c.corner},
	}
	for _, row := range required {
		value, ok := layoutConstant(in.Profile, row.name)
		if !ok {
			return mindmapConstants{}, errMindmapDomain
		}
		*row.into = value
	}
	if in.Profile == scene.ProfileVector {
		return c, c.applyConfig(in.Options.Config)
	}
	return c, nil
}

func (c *mindmapConstants) applyConfig(entries []scene.Config) error {
	for _, entry := range entries {
		target := map[string]*int32{mindmapPaddingKey: &c.padding, mindmapMaxWidth: &c.maxWidth}[entry.Key]
		if target == nil {
			continue
		}
		px, err := strconv.ParseInt(entry.Value, 10, 64)
		if err != nil || px < 0 || px*pixelUnits > int64(geom.CoordLimit) {
			return geom.ErrOverflow
		}
		*target = int32(px * pixelUnits)
	}
	return nil
}

func mindmapMetric(profile scene.Profile) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	return measure.ForRole(measure.RoleLabel)
}

type mindmapPlan struct {
	in     Input
	c      mindmapConstants
	index  map[string]int
	labels map[string]string
	lines  [][]measure.StyledLine
	nodes  []tree.Node
}

func newMindmapPlan(in Input) (*mindmapPlan, error) {
	if err := mindmapLimits(in); err != nil {
		return nil, err
	}
	c, err := loadMindmapConstants(in)
	if err != nil {
		return nil, err
	}
	p := &mindmapPlan{in: in, c: c, index: make(map[string]int, len(in.Boxes)), labels: make(map[string]string, len(in.Labels))}
	for i, box := range in.Boxes {
		p.index[box.ID] = i
	}
	for _, label := range in.Labels {
		p.labels[label.Owner] = label.Text
	}
	return p, p.measure()
}

func mindmapLimits(in Input) error {
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

func (p *mindmapPlan) labelText(box Box) string {
	if text, ok := p.labels[box.ID]; ok {
		return text
	}
	return box.ID
}

func (p *mindmapPlan) measure() error {
	parents := make([]int, len(p.in.Boxes))
	for i := range parents {
		parents[i] = tree.NoParent
	}
	for _, route := range p.in.Routes {
		parents[p.index[route.To]] = p.index[route.From]
	}
	wrap := max(p.c.maxWidth-2*p.c.padding, 1)
	for i, box := range p.in.Boxes {
		lines, err := measure.StyledLines(p.labelText(box), wrap, mindmapMetric(p.in.Profile).WithFontFamily(p.in.Options.FontFamily))
		if err != nil {
			return geom.ErrOverflow
		}
		w, h, err := p.boxSize(lines)
		if err != nil {
			return err
		}
		p.lines = append(p.lines, lines)
		p.nodes = append(p.nodes, tree.Node{Parent: parents[i], Width: w, Height: h})
	}
	return nil
}

func (p *mindmapPlan) boxSize(lines []measure.StyledLine) (int32, int32, error) {
	textWidth := int64(widestLine(lines))
	w := min(int64(p.c.maxWidth), textWidth+2*int64(p.c.padding))
	h := int64(max(len(lines), 1))*int64(p.c.lineHeight) + 2*int64(p.c.padding)
	if h > geom.CoordLimit || w > geom.CoordLimit {
		return 0, 0, geom.ErrOverflow
	}
	return int32(max(w, 1)), int32(max(h, 1)), nil
}

func layoutMindmap(in Input) (scene.Scene, []diag.Diagnostic, error) {
	in.Options = resolveOptions(in.Options)
	p, err := newMindmapPlan(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	placed, err := tree.Mindmap(p.nodes, tree.Gaps{Level: p.c.levelGap, Sibling: p.c.siblingGap})
	if err != nil {
		return scene.Scene{}, nil, err
	}
	canvas, err := tree.Normalize(&placed, p.c.margin)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := blankMindmapDump(in)
	dump.Canvas = canvas
	for i := range dump.Boxes {
		dump.Boxes[i].Rect = placed.Boxes[i]
	}
	for i, route := range in.Routes {
		dump.Routes[i].Points = placed.Routes[p.index[route.To]]
	}
	return scene.Scene{Dump: dump, Groups: p.groups(dump)}, nil, nil
}

func blankMindmapDump(in Input) scene.Dump {
	options := in.Options
	options.Profile, options.Direction = in.Profile, in.Direction
	d := scene.Dump{Kind: mindmapKind, Options: options}
	for _, box := range in.Boxes {
		d.Boxes = append(d.Boxes, scene.Box{ID: box.ID, Role: box.Role, Exclusive: box.Exclusive})
	}
	for _, route := range in.Routes {
		d.Routes = append(d.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: route.Orthogonal})
	}
	return d
}
