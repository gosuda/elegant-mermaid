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
	tvmodel "github.com/gosuda/elegant-mermaid/internal/model/treeview"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	tvparser "github.com/gosuda/elegant-mermaid/internal/syntax/treeview"
)

const (
	treeviewKind      = "treeview"
	treeviewDirectory = "directory"
	treeviewFile      = "file"
	treeviewHighlight = "highlight"
	treeviewMilli     = 1000
	treeviewLevelCell = 4
	suffixName        = ".label"
	suffixDesc        = ".desc"
	suffixIcon        = ".icon"
	suffixClass       = ".class"
)

type treeviewModel = tvmodel.Model

var errTreeviewDomain = errors.New("treeview layout: invalid geometry")

func (d *Diagram) resolveTreeview() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := tvparser.Parse(d.Source, d.Preprocessing.Removed)
	d.treeview, resolved = tvmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.treeview.AccTitle, d.treeview.AccDescr
	return parsed, resolved
}

func (d *Diagram) treeviewInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromTreeview(d.treeview, profile, options)
	return input, diagnostics, nil
}

func treeviewBoxID(index int) string { return "n" + strconv.Itoa(index) }

func treeviewConfig(c tvmodel.Config) []scene.Config {
	var out []scene.Config
	for _, field := range []struct {
		key    string
		length tvmodel.Length
	}{{"lineThickness", c.LineThickness}, {"paddingX", c.PaddingX}, {"paddingY", c.PaddingY}, {"rowIndent", c.RowIndent}} {
		if field.length.Set {
			out = append(out, scene.ConfigInt(field.key, field.length.Thousandths))
		}
	}
	return out
}

func FromTreeview(m *tvmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = treeviewConfig(m.Config)
	options.Profile = profile
	in := Input{Kind: treeviewKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	for _, node := range m.Nodes {
		id := treeviewBoxID(node.Index)
		shape := treeviewFile
		if node.Directory {
			shape = treeviewDirectory
		}
		in.Boxes = append(in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: shape, Exclusive: true})
		in.Labels = append(in.Labels, treeviewLabels(id, node)...)
		if node.Parent != tvmodel.NoParent {
			in.Routes = append(in.Routes, Route{ID: "e" + strconv.Itoa(len(in.Routes)), From: treeviewBoxID(node.Parent), To: id, Orthogonal: true, Line: "normal"})
		}
	}
	return in, nil
}

func treeviewLabels(id string, node tvmodel.Node) []Label {
	out := []Label{{ID: id + suffixName, Owner: id, Role: scene.TextRoleLabel, Text: node.Name}}
	for _, extra := range []struct{ suffix, text string }{{suffixDesc, node.Description}, {suffixIcon, node.Icon}, {suffixClass, node.Class}} {
		if extra.text != "" {
			out = append(out, Label{ID: id + extra.suffix, Owner: id, Role: scene.TextRoleBody, Text: extra.text})
		}
	}
	return out
}

type treeviewNode struct {
	name, desc, icon, class string
	directory, root         bool
}

func (n *treeviewNode) assign(label Label) {
	switch {
	case strings.HasSuffix(label.ID, suffixName):
		n.name = label.Text
	case strings.HasSuffix(label.ID, suffixDesc):
		n.desc = label.Text
	case strings.HasSuffix(label.ID, suffixIcon):
		if label.Text != tvmodel.IconNone {
			n.icon = label.Text
		}
	case strings.HasSuffix(label.ID, suffixClass):
		n.class = label.Text
	}
}

func flatten(text string) string { return strings.ReplaceAll(text, "\n", " ") }

func (n treeviewNode) shown(profile scene.Profile) string {
	if profile == scene.ProfileCell && n.directory && !n.root {
		return flatten(n.name) + "/"
	}
	return flatten(n.name)
}

func (n treeviewNode) role() scene.TextRole {
	if n.directory {
		return scene.TextRoleLabel
	}
	return scene.TextRoleBody
}

func (n treeviewNode) metric(profile scene.Profile) measure.Metric {
	if profile == scene.ProfileCell {
		return measure.CellMetric()
	}
	if n.directory {
		return measure.ForRole(measure.RoleLabel)
	}
	return measure.ForRole(measure.RoleBody)
}

type treeviewPlan struct {
	in    Input
	m     tree.ViewMetrics
	index map[string]int
	nodes []treeviewNode
	rows  []tree.ViewRow
}

func treeviewLimits(in Input) error {
	if nodes := int64(len(in.Boxes)); nodes > int64(in.Options.Limits.MaxNodes) {
		return &layered.LimitError{Resource: "nodes", Limit: int64(in.Options.Limits.MaxNodes), Actual: nodes}
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

func treeviewMetrics(in Input) (tree.ViewMetrics, error) {
	var m tree.ViewMetrics
	required := []struct {
		name string
		into *int32
	}{
		{"treeview.row_indent", &m.RowIndent}, {"treeview.padding_x", &m.PaddingX}, {"treeview.padding_y", &m.PaddingY},
		{"treeview.line_thickness", &m.Thickness}, {"treeview.icon_size", &m.IconSize}, {"treeview.icon_gap", &m.IconGap},
		{"treeview.desc_gap", &m.DescGap}, {"line_h", &m.TextHeight}, {"canvas_margin", &m.Margin},
	}
	for _, row := range required {
		value, ok := layoutConstant(in.Profile, row.name)
		if !ok {
			return tree.ViewMetrics{}, errTreeviewDomain
		}
		*row.into = value
	}
	if in.Profile == scene.ProfileVector {
		return m, applyTreeviewConfig(&m, in.Options.Config)
	}
	return m, nil
}

func applyTreeviewConfig(m *tree.ViewMetrics, entries []scene.Config) error {
	targets := map[string]*int32{"rowIndent": &m.RowIndent, "paddingX": &m.PaddingX, "paddingY": &m.PaddingY, "lineThickness": &m.Thickness}
	for _, entry := range entries {
		target := targets[entry.Key]
		if target == nil {
			continue
		}
		thousandths, err := strconv.ParseInt(entry.Value, 10, 64)
		if err != nil || thousandths < 0 || thousandths > geom.CoordLimit {
			return geom.ErrOverflow
		}
		units := geom.FloorDiv(2*thousandths*pixelUnits+treeviewMilli, 2*treeviewMilli)
		if units > geom.CoordLimit {
			return geom.ErrOverflow
		}
		*target = int32(units)
	}
	return nil
}

func newTreeviewPlan(in Input) (*treeviewPlan, error) {
	if err := treeviewLimits(in); err != nil {
		return nil, err
	}
	m, err := treeviewMetrics(in)
	if err != nil {
		return nil, err
	}
	p := &treeviewPlan{in: in, m: m, index: make(map[string]int, len(in.Boxes)), nodes: make([]treeviewNode, len(in.Boxes))}
	for i, box := range in.Boxes {
		p.index[box.ID] = i
		p.nodes[i] = treeviewNode{name: box.ID, directory: box.Shape == treeviewDirectory}
	}
	for _, label := range in.Labels {
		i, ok := p.index[label.Owner]
		if !ok {
			return nil, errTreeviewDomain
		}
		p.nodes[i].assign(label)
	}
	return p, p.measure()
}

func (p *treeviewPlan) parents() ([]int, error) {
	parents := make([]int, len(p.in.Boxes))
	for i := range parents {
		parents[i] = tree.NoParent
	}
	for _, route := range p.in.Routes {
		from, fromOK := p.index[route.From]
		to, toOK := p.index[route.To]
		if !fromOK || !toOK {
			return nil, errTreeviewDomain
		}
		parents[to] = from
	}
	return parents, nil
}

func (p *treeviewPlan) measure() error {
	parents, err := p.parents()
	if err != nil {
		return err
	}
	desc := measure.ForRole(measure.RoleBody)
	if p.in.Profile == scene.ProfileCell {
		desc = measure.CellMetric()
	}
	desc = desc.WithFontFamily(p.in.Options.FontFamily)
	for i := range p.nodes {
		node := &p.nodes[i]
		node.root = parents[i] == tree.NoParent
		row := tree.ViewRow{Parent: parents[i], HasDesc: node.desc != "", HasIcon: node.icon != ""}
		if row.LabelWidth, err = node.metric(p.in.Profile).WithFontFamily(p.in.Options.FontFamily).TextWidth(node.shown(p.in.Profile)); err != nil {
			return geom.ErrOverflow
		}
		if row.DescWidth, err = desc.TextWidth(flatten(node.desc)); err != nil {
			return geom.ErrOverflow
		}
		p.rows = append(p.rows, row)
	}
	return nil
}

func layoutTreeview(in Input) (scene.Scene, []diag.Diagnostic, error) {
	in.Options = resolveOptions(in.Options)
	p, err := newTreeviewPlan(in)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	placed, err := tree.TreeView(p.rows, p.m)
	if err != nil {
		return scene.Scene{}, nil, err
	}
	dump := blankTreeviewDump(in)
	dump.Canvas = placed.Canvas
	for i := range dump.Boxes {
		dump.Boxes[i].Rect = placed.Boxes[i]
	}
	for i, route := range in.Routes {
		dump.Routes[i].Points = placed.Routes[p.index[route.To]]
	}
	groups, diagnostics := p.groups(dump, placed)
	return scene.Scene{Dump: dump, Groups: groups}, diagnostics, nil
}

func blankTreeviewDump(in Input) scene.Dump {
	options := in.Options
	options.Profile, options.Direction = in.Profile, in.Direction
	d := scene.Dump{Kind: treeviewKind, Options: options}
	for _, box := range in.Boxes {
		d.Boxes = append(d.Boxes, scene.Box{ID: box.ID, Role: box.Role, Exclusive: box.Exclusive})
	}
	for _, route := range in.Routes {
		d.Routes = append(d.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: route.Orthogonal})
	}
	return d
}
