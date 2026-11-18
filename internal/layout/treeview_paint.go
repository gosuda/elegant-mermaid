package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/layout/tree"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	treeviewIconBox  = 1536
	treeviewTextSize = 14
)

func (p *treeviewPlan) groups(dump scene.Dump, placed tree.ViewLayout) ([]*scene.Group, []diag.Diagnostic) {
	groups := make([]*scene.Group, 0, len(dump.Routes)+len(dump.Boxes))
	for _, route := range dump.Routes {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: route.ID, Items: p.guide(route.Points)})
	}
	var diagnostics []diag.Diagnostic
	prefixes := tree.TreePrefixes(p.rows)
	for i, box := range dump.Boxes {
		items, missing := p.node(i, placed, prefixes[i])
		diagnostics = append(diagnostics, missing...)
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: box.ID, Items: items})
	}
	return groups, diagnostics
}

func (p *treeviewPlan) guide(points []geom.Point) []scene.Primitive {
	if p.in.Profile == scene.ProfileCell {
		return nil
	}
	width := scene.Width{Kind: scene.WidthUnits, Units: p.m.Thickness}
	return []scene.Primitive{&scene.Polyline{Shape: scene.Shape{Style: "rule", Width: width}, Points: points}}
}

func (p *treeviewPlan) node(i int, placed tree.ViewLayout, prefix string) ([]scene.Primitive, []diag.Diagnostic) {
	node, rect := p.nodes[i], placed.Boxes[i]
	var items []scene.Primitive
	if node.class == treeviewHighlight && p.in.Profile == scene.ProfileVector {
		band := geom.Rect{X: rect.X, Y: rect.Y, W: placed.Right - rect.X, H: rect.H}
		items = append(items, &scene.Rect{Shape: scene.Shape{Style: "band"}, Rect: band})
	}
	var diagnostics []diag.Diagnostic
	if node.icon != "" {
		drawing := icon.Draw(p.in.IconPacks, node.icon, p.iconAt(i, rect, placed), p.in.Profile)
		items = append(items, drawing.Items...)
		if drawing.Missing {
			diagnostics = append(diagnostics, icon.MissingDiagnostic(node.icon, source.Span{}))
		}
	}
	return append(items, p.texts(i, placed, prefix)...), diagnostics
}

func (p *treeviewPlan) texts(i int, placed tree.ViewLayout, prefix string) []scene.Primitive {
	node, row := p.nodes[i], p.rows[i]
	y := placed.Boxes[i].Y + p.m.PaddingY
	var out []scene.Primitive
	if p.in.Profile == scene.ProfileCell && prefix != "" {
		out = append(out, p.text(geom.Rect{X: placed.Boxes[0].X, Y: y, W: int32(treeviewLevelCell * placed.Depth[i]), H: p.m.TextHeight}, scene.TextRoleBody, "text", scene.Run{Text: prefix}))
	}
	out = append(out, p.text(geom.Rect{X: placed.LabelX[i], Y: y, W: row.LabelWidth, H: p.m.TextHeight}, node.role(), "text", scene.Run{Text: node.shown(p.in.Profile)}))
	if node.desc != "" {
		out = append(out, p.text(geom.Rect{X: placed.DescX, Y: y, W: row.DescWidth, H: p.m.TextHeight}, scene.TextRoleBody, "text-muted", scene.Run{Text: flatten(node.desc), Italic: true}))
	}
	return out
}

func (p *treeviewPlan) iconAt(i int, rect geom.Rect, placed tree.ViewLayout) geom.Point {
	if p.in.Profile == scene.ProfileCell {
		return geom.Point{X: placed.IconX[i], Y: rect.Y}
	}
	centre := geom.Point{X: placed.IconX[i] + p.m.IconSize/2, Y: rect.Y + rect.H/2}
	return geom.Point{X: centre.X - treeviewIconBox/2, Y: centre.Y - treeviewIconBox/2}
}

func (p *treeviewPlan) text(rect geom.Rect, role scene.TextRole, style string, run scene.Run) *scene.Text {
	return &scene.Text{Rect: rect, Role: role, Size: treeviewTextSize, Align: scene.AlignStart, Style: style, Lines: [][]scene.Run{{run}}}
}
