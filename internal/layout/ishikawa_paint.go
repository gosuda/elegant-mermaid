package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *ishikawaPlan) groups(dump scene.Dump) []*scene.Group {
	groups := make([]*scene.Group, 0, len(dump.Routes)+p.count)
	for i, route := range dump.Routes {
		items := []scene.Primitive{&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Points: route.Points}}
		if marker := p.in.Routes[i].MarkerStart; marker != "" {
			items = append(items, &scene.MarkerRef{Marker: marker, At: route.Points[0], Axis: ishikawaAxis(route.Points[1], route.Points[0])})
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: route.ID, Items: items})
	}
	for i := range p.count {
		box := dump.Boxes[i]
		items := append(p.outline(i, box.Rect), p.text(box.Rect, p.lines[i]))
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: box.ID, Items: items})
	}
	return groups
}

func ishikawaAxis(from, to geom.Point) scene.Axis {
	dx, dy := int64(to.X)-int64(from.X), int64(to.Y)-int64(from.Y)
	horizontal := max(dx, -dx) >= max(dy, -dy)
	switch {
	case horizontal && dx < 0:
		return scene.AxisMinusX
	case horizontal:
		return scene.AxisPlusX
	case dy < 0:
		return scene.AxisMinusY
	}
	return scene.AxisPlusY
}

func (p *ishikawaPlan) outline(index int, rect geom.Rect) []scene.Primitive {
	shape := scene.Shape{Style: "node"}
	switch p.depth[index] {
	case 0:
		shape.Width = scene.Width{Kind: scene.WidthEmphasis}
		if p.in.Profile == scene.ProfileVector {
			return []scene.Primitive{&scene.RoundRect{Shape: shape, Rect: rect, R: p.c.corner}}
		}
	case 1:
	default:
		return nil
	}
	return []scene.Primitive{&scene.Rect{Shape: shape, Rect: rect}}
}

func (p *ishikawaPlan) text(rect geom.Rect, lines []measure.StyledLine) *scene.Text {
	height := int32(len(lines)) * p.c.lineHeight
	box := geom.Rect{X: rect.X, Y: rect.Y + int32(geom.FloorDiv(int64(rect.H-height), 2)), W: rect.W, H: height}
	return &scene.Text{Rect: box, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: sequenceRuns(lines)}
}
