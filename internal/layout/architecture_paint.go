package layout

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *archPlanner) sceneGroups() []*scene.Group {
	var groups []*scene.Group
	for k, i := range p.groupAt {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: p.in.Boxes[i].ID, Items: p.frameItems(k)})
	}
	for i, route := range p.in.Routes {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: route.ID, Items: p.edgeItems(i, route)})
	}
	for k, i := range p.nodeAt {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: p.in.Boxes[i].ID, Items: p.nodeItems(k)})
	}
	return groups
}

func (p *archPlanner) text(rect geom.Rect, lines []measure.StyledLine, align scene.Align) scene.Primitive {
	return &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 14, Align: align, Style: "text", Lines: sequenceRuns(lines)}
}

func (p *archPlanner) frameItems(group int) []scene.Primitive {
	items := []scene.Primitive{&scene.Rect{Shape: plainShape("group"), Rect: p.result.Frames[group]}}
	if lines := p.titles[group]; len(lines) > 0 {
		items = append(items, p.text(p.result.Titles[group], lines, scene.AlignStart))
	}
	return items
}

func (p *archPlanner) edgeItems(index int, route Route) []scene.Primitive {
	var items []scene.Primitive
	if points := p.result.Routes[index]; len(points) >= 2 {
		items = append(items, &scene.Polyline{Shape: plainShape("edge"), Corner: p.c.corner, Points: slices.Clone(points)})
		end := len(points) - 1
		if route.MarkerStart != "" {
			items = append(items, &scene.MarkerRef{Marker: route.MarkerStart, At: points[0], Axis: blockAxis(points[1], points[0])})
		}
		if route.MarkerEnd != "" {
			items = append(items, &scene.MarkerRef{Marker: route.MarkerEnd, At: points[end], Axis: blockAxis(points[end-1], points[end])})
		}
	}
	if lines := p.edgeLabels[index]; len(lines) > 0 {
		items = append(items, p.text(p.result.EdgeLabels[index], lines, scene.AlignMiddle))
	}
	return items
}

func (p *archPlanner) nodeItems(node int) []scene.Primitive {
	box, icon := p.result.Boxes[node], p.result.Icons[node]
	if p.specs[node].Kind == "junction" {
		return p.junctionItems(box)
	}
	items := p.outline(icon)
	if lines := p.iconTexts[node]; len(lines) > 0 {
		items = append(items, p.iconTextItem(icon, lines))
	}
	if lines := p.labels[node]; len(lines) > 0 {
		items = append(items, p.text(p.result.Labels[node], lines, scene.AlignMiddle))
	}
	return items
}

func (p *archPlanner) outline(icon geom.Rect) []scene.Primitive {
	if p.profile == scene.ProfileCell {
		return []scene.Primitive{&scene.Rect{Shape: plainShape("node"), Rect: icon}}
	}
	return []scene.Primitive{&scene.RoundRect{Shape: plainShape("node"), Rect: icon, R: min(p.c.corner, icon.W/2, icon.H/2)}}
}

func (p *archPlanner) junctionItems(box geom.Rect) []scene.Primitive {
	if p.profile == scene.ProfileCell {
		return []scene.Primitive{&scene.SymbolRef{Symbol: "disc", At: geom.Point{X: box.X, Y: box.Y}, Style: "ink"}}
	}
	return []scene.Primitive{&scene.Ellipse{Shape: plainShape("ink"), CX: box.X + box.W/2, CY: box.Y + box.H/2, RX: box.W / 2, RY: box.H / 2}}
}

func (p *archPlanner) iconTextItem(icon geom.Rect, lines []measure.StyledLine) scene.Primitive {
	params := p.c.params
	room := max(1, (icon.H-2*p.c.border)/params.LineHeight)
	lines = lines[:min(int(room), len(lines))]
	height := int32(len(lines)) * params.LineHeight
	rect := geom.Rect{X: icon.X + params.Inset, Y: icon.Y + p.c.border + half(icon.H-2*p.c.border-height), W: max(icon.W-2*params.Inset, 1), H: height}
	return p.text(rect, lines, scene.AlignMiddle)
}
