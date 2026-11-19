package layout

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *blockPlanner) groups() []*scene.Group {
	var groups []*scene.Group
	for i, box := range p.in.Boxes {
		if box.Role == scene.RoleGroup {
			groups = append(groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: box.ID, Items: p.frame(i)})
		}
	}
	for i, route := range p.in.Routes {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: route.ID, Items: p.edgeItems(i, route)})
	}
	for i, box := range p.in.Boxes {
		if box.Role == scene.RoleNode && p.specs[i].Type != "space" {
			groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: box.ID, Items: p.nodeItems(i)})
		}
	}
	return groups
}

func (p *blockPlanner) frame(index int) []scene.Primitive {
	if index == 0 {
		return nil
	}
	return []scene.Primitive{&scene.Rect{Shape: plainShape("group"), Rect: p.dump.Boxes[index].Rect}}
}

func (p *blockPlanner) edgeItems(index int, route Route) []scene.Primitive {
	var items []scene.Primitive
	if points := p.dump.Routes[index].Points; len(points) >= 2 {
		items = p.routeItems(route, points)
	}
	if position := p.labelOf(route.ID); position >= 0 {
		items = append(items, p.labelItem(position))
	}
	return items
}

func (p *blockPlanner) routeItems(route Route, points []geom.Point) []scene.Primitive {
	shape := plainShape("edge")
	switch route.Line {
	case "thick":
		shape.Width.Kind = scene.WidthEmphasis
	case "dotted":
		shape.Line = scene.LineDotted
	}
	items := []scene.Primitive{&scene.Polyline{Shape: shape, Corner: p.corner, Points: slices.Clone(points)}}
	end := len(points) - 1
	if route.MarkerStart != "" {
		items = append(items, &scene.MarkerRef{Marker: route.MarkerStart, At: points[0], Axis: blockAxis(points[1], points[0])})
	}
	if route.MarkerEnd != "" {
		items = append(items, &scene.MarkerRef{Marker: route.MarkerEnd, At: points[end], Axis: blockAxis(points[end-1], points[end])})
	}
	return items
}

func blockAxis(from, to geom.Point) scene.Axis {
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

func (p *blockPlanner) labelItem(position int) scene.Primitive {
	return &scene.Text{Rect: p.dump.Labels[position].Rect, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: sequenceRuns(p.labelLines[position])}
}

func (p *blockPlanner) nodeItems(index int) []scene.Primitive {
	rect := p.dump.Boxes[index].Rect
	lines := p.lines[index]
	textH := int32(len(lines)) * p.lineHeight
	text := &scene.Text{Rect: geom.Rect{X: rect.X, Y: rect.Y + half(rect.H-textH), W: rect.W, H: textH}, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: sequenceRuns(lines)}
	return append(p.outline(p.specs[index], rect), text)
}

func (p *blockPlanner) outline(spec blockShapeSpec, rect geom.Rect) []scene.Primitive {
	if p.profile == scene.ProfileCell {
		return cellOutline(spec, rect)
	}
	return p.vectorOutline(spec, rect)
}

func cellOutline(spec blockShapeSpec, rect geom.Rect) []scene.Primitive {
	shape := plainShape("node")
	switch spec.Type {
	case "roundedRect", "stadium", "circle":
		return []scene.Primitive{&scene.RoundRect{Shape: shape, Rect: rect}}
	case "cylinder":
		return blockCylinder(rect, scene.ProfileCell)
	case "doublecircle":
		shape.Line = scene.LineDouble
	case "block_arrow":
		return append([]scene.Primitive{&scene.Rect{Shape: shape, Rect: rect}}, blockArrowMarkers(blockHeads(spec.Directions), rect)...)
	}
	return []scene.Primitive{&scene.Rect{Shape: shape, Rect: rect}}
}

func blockCylinder(rect geom.Rect, profile scene.Profile) []scene.Primitive {
	items, err := c4CylinderOutline(rect, profile, int64(rect.H))
	if err != nil {
		return []scene.Primitive{&scene.RoundRect{Shape: plainShape("node"), Rect: rect}}
	}
	return items
}

type blockHeadSet struct{ up, right, down, left bool }

func blockHeads(directions []string) blockHeadSet {
	var heads blockHeadSet
	for _, direction := range directions {
		heads.up = heads.up || direction == "up" || direction == "y"
		heads.down = heads.down || direction == "down" || direction == "y"
		heads.left = heads.left || direction == "left" || direction == "x"
		heads.right = heads.right || direction == "right" || direction == "x"
	}
	return heads
}

func blockArrowMarkers(heads blockHeadSet, rect geom.Rect) []scene.Primitive {
	cx, cy := rect.X+rect.W/2, rect.Y+rect.H/2
	right, bottom := rect.X+rect.W-1, rect.Y+rect.H-1
	var items []scene.Primitive
	for _, head := range []struct {
		on   bool
		at   geom.Point
		axis scene.Axis
	}{
		{heads.up, geom.Point{X: cx, Y: rect.Y}, scene.AxisMinusY},
		{heads.right, geom.Point{X: right, Y: cy}, scene.AxisPlusX},
		{heads.down, geom.Point{X: cx, Y: bottom}, scene.AxisPlusY},
		{heads.left, geom.Point{X: rect.X, Y: cy}, scene.AxisMinusX},
	} {
		if head.on {
			items = append(items, &scene.MarkerRef{Marker: "point", At: head.at, Axis: head.axis})
		}
	}
	return items
}

type blockBounds struct{ x, y, w, h, slant int64 }

func (b blockBounds) right() int64  { return b.x + b.w }
func (b blockBounds) bottom() int64 { return b.y + b.h }
func (b blockBounds) midX() int64   { return b.x + b.w/2 }
func (b blockBounds) midY() int64   { return b.y + b.h/2 }

var blockPolygons = map[string]func(blockBounds) [][2]int64{
	"diamond": func(b blockBounds) [][2]int64 {
		return [][2]int64{{b.midX(), b.y}, {b.right(), b.midY()}, {b.midX(), b.bottom()}, {b.x, b.midY()}}
	},
	"hexagon": func(b blockBounds) [][2]int64 {
		return [][2]int64{{b.x + b.slant, b.y}, {b.right() - b.slant, b.y}, {b.right(), b.midY()}, {b.right() - b.slant, b.bottom()}, {b.x + b.slant, b.bottom()}, {b.x, b.midY()}}
	},
	"lean_right": func(b blockBounds) [][2]int64 {
		return [][2]int64{{b.x + b.slant, b.y}, {b.right(), b.y}, {b.right() - b.slant, b.bottom()}, {b.x, b.bottom()}}
	},
	"lean_left": func(b blockBounds) [][2]int64 {
		return [][2]int64{{b.x, b.y}, {b.right() - b.slant, b.y}, {b.right(), b.bottom()}, {b.x + b.slant, b.bottom()}}
	},
	"trapezoid": func(b blockBounds) [][2]int64 {
		return [][2]int64{{b.x + b.slant, b.y}, {b.right() - b.slant, b.y}, {b.right(), b.bottom()}, {b.x, b.bottom()}}
	},
	"inv_trapezoid": func(b blockBounds) [][2]int64 {
		return [][2]int64{{b.x, b.y}, {b.right(), b.y}, {b.right() - b.slant, b.bottom()}, {b.x + b.slant, b.bottom()}}
	},
	"odd": func(b blockBounds) [][2]int64 {
		return [][2]int64{{b.x, b.y}, {b.right(), b.y}, {b.right(), b.bottom()}, {b.x, b.bottom()}, {b.x + b.slant, b.midY()}}
	},
}

func (p *blockPlanner) vectorOutline(spec blockShapeSpec, rect geom.Rect) []scene.Primitive {
	shape := plainShape("node")
	bounds := blockBounds{x: int64(rect.X), y: int64(rect.Y), w: int64(rect.W), h: int64(rect.H)}
	bounds.slant = min(bounds.h/4, bounds.w/4)
	if build, ok := blockPolygons[spec.Type]; ok {
		return blockPolygon(shape, build(bounds))
	}
	switch spec.Type {
	case "roundedRect":
		return []scene.Primitive{&scene.RoundRect{Shape: shape, Rect: rect, R: min(p.corner, rect.W/2, rect.H/2)}}
	case "stadium":
		return []scene.Primitive{&scene.RoundRect{Shape: shape, Rect: rect, R: min(rect.W, rect.H) / 2}}
	case "circle":
		return []scene.Primitive{blockEllipse(shape, rect, 0)}
	case "doublecircle":
		return []scene.Primitive{blockEllipse(shape, rect, 0), blockEllipse(shape, rect, min(blockRingInset, rect.W/4, rect.H/4))}
	case "cylinder":
		return blockCylinder(rect, scene.ProfileVector)
	case "subroutine":
		return subroutineOutline(rect)
	case "block_arrow":
		return blockPolygon(shape, blockArrowPoints(blockHeads(spec.Directions), rect))
	}
	return []scene.Primitive{&scene.Rect{Shape: shape, Rect: rect}}
}

const blockRingInset = 256

func blockEllipse(shape scene.Shape, rect geom.Rect, inset int32) scene.Primitive {
	return &scene.Ellipse{Shape: shape, CX: rect.X + rect.W/2, CY: rect.Y + rect.H/2, RX: rect.W/2 - inset, RY: rect.H/2 - inset}
}

func blockPolygon(shape scene.Shape, coordinates [][2]int64) []scene.Primitive {
	points := make([]geom.Point, len(coordinates))
	for i, c := range coordinates {
		points[i] = geom.Point{X: int32(c[0]), Y: int32(c[1])}
	}
	return []scene.Primitive{&scene.Polygon{Shape: shape, Points: points}}
}

func subroutineOutline(rect geom.Rect) []scene.Primitive {
	inset := min(512, rect.W/4)
	items := []scene.Primitive{&scene.Rect{Shape: plainShape("node"), Rect: rect}}
	for _, x := range []int32{rect.X + inset, rect.X + rect.W - inset} {
		items = append(items, &scene.Polyline{Shape: plainShape("rule"), Points: []geom.Point{{X: x, Y: rect.Y}, {X: x, Y: rect.Y + rect.H}}})
	}
	return items
}

func blockArrowPoints(heads blockHeadSet, rect geom.Rect) [][2]int64 {
	b := blockBounds{x: int64(rect.X), y: int64(rect.Y), w: int64(rect.W), h: int64(rect.H)}
	depth := min(b.w, b.h) / 4
	left, right, top, bottom := b.x, b.right(), b.y, b.bottom()
	if heads.left {
		left += depth
	}
	if heads.right {
		right -= depth
	}
	if heads.up {
		top += depth
	}
	if heads.down {
		bottom -= depth
	}
	points := [][2]int64{{left, top}}
	if heads.up {
		points = append(points, [2]int64{b.midX(), b.y})
	}
	points = append(points, [2]int64{right, top})
	if heads.right {
		points = append(points, [2]int64{b.right(), b.midY()})
	}
	points = append(points, [2]int64{right, bottom})
	if heads.down {
		points = append(points, [2]int64{b.midX(), b.bottom()})
	}
	points = append(points, [2]int64{left, bottom})
	if heads.left {
		points = append(points, [2]int64{b.x, b.midY()})
	}
	return points
}
