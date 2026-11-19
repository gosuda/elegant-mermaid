package layout

import (
	"math"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func c4ShapeScene(in Input, s *scene.Scene) error {
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleNode {
			continue
		}
		node := c4Node(in.Boxes, group.Owner)
		if node == nil || node.Shape == "rect" {
			continue
		}
		for _, box := range s.Boxes {
			if box.ID != node.ID {
				continue
			}
			if err := c4ReplaceFrame(group, box.Rect, node.Shape, in.Profile); err != nil {
				return err
			}
		}
	}
	return nil
}

func c4Node(boxes []Box, id string) *Box {
	for i := range boxes {
		if boxes[i].ID == id && boxes[i].Role == scene.RoleNode {
			return &boxes[i]
		}
	}
	return nil
}

func c4TextTopGap(items []scene.Primitive, top int32) int64 {
	gap, found := int64(0), false
	for _, item := range items {
		text, ok := item.(*scene.Text)
		if !ok {
			continue
		}
		d := int64(text.Rect.Y) - int64(top)
		if !found || d < gap {
			gap, found = d, true
		}
	}
	return max(gap, 0)
}

func c4ReplaceFrame(group *scene.Group, rect geom.Rect, kind string, profile scene.Profile) error {
	gap := c4TextTopGap(group.Items, rect.Y)
	var shapes []scene.Primitive
	var err error
	switch kind {
	case "person":
		shapes, err = c4PersonOutline(rect, profile, gap)
	case "cyl":
		shapes, err = c4CylinderOutline(rect, profile, gap)
	default:
		return nil
	}
	if err != nil {
		return err
	}
	items := make([]scene.Primitive, 0, len(group.Items)+len(shapes))
	replaced := false
	for _, item := range group.Items {
		if !replaced && c4IsFrame(item, rect) {
			items = append(items, shapes...)
			replaced = true
			continue
		}
		items = append(items, item)
	}
	group.Items = items
	return nil
}

func c4IsFrame(item scene.Primitive, rect geom.Rect) bool {
	switch p := item.(type) {
	case *scene.Rect:
		return p.Rect == rect
	case *scene.RoundRect:
		return p.Rect == rect
	default:
		return false
	}
}

func c4Coordinate(v int64) (int32, error) {
	if v < math.MinInt32 || v > math.MaxInt32 {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}

func c4PersonOutline(rect geom.Rect, profile scene.Profile, gap int64) ([]scene.Primitive, error) {
	w, h := int64(rect.W), int64(rect.H)
	r := max(0, min(max(16*64, min(w*23/100, 56*64)), w/2, h/2, gap/2))
	offset := r * 173 / 100
	body := rect
	var err error
	body.Y, err = c4Coordinate(int64(rect.Y) + offset)
	if err != nil {
		return nil, err
	}
	body.H, err = c4Coordinate(h - offset)
	if err != nil {
		return nil, err
	}
	br := int32(0)
	if profile != scene.ProfileCell {
		br, err = c4Coordinate(min(w*177/1000, (h-offset)*45/100))
		if err != nil {
			return nil, err
		}
	}
	cx, err := c4Coordinate(int64(rect.X) + w/2)
	if err != nil {
		return nil, err
	}
	cy, err := c4Coordinate(int64(rect.Y) + r)
	if err != nil {
		return nil, err
	}
	radius, err := c4Coordinate(r)
	if err != nil {
		return nil, err
	}
	shape := scene.Shape{Style: "node"}
	return []scene.Primitive{&scene.RoundRect{Shape: shape, Rect: body, R: br}, &scene.Ellipse{Shape: shape, CX: cx, CY: cy, RX: radius, RY: radius}}, nil
}

func c4CylinderOutline(rect geom.Rect, profile scene.Profile, gap int64) ([]scene.Primitive, error) {
	w, h := int64(rect.W), int64(rect.H)
	r := max(0, min(w*1600/(8000+w), h/4, gap/2))
	shape := scene.Shape{Style: "node"}
	var outer scene.Primitive = &scene.RoundRect{Shape: shape, Rect: rect}
	var err error
	if profile != scene.ProfileCell {
		outer, err = c4CylinderPath(rect, r)
		if err != nil {
			return nil, err
		}
	}
	cx, err := c4Coordinate(int64(rect.X) + w/2)
	if err != nil {
		return nil, err
	}
	cy, err := c4Coordinate(int64(rect.Y) + r)
	if err != nil {
		return nil, err
	}
	rx := w / 2
	if profile == scene.ProfileCell {
		rx = max(w-1, 0) / 2
	}
	xradius, err := c4Coordinate(rx)
	if err != nil {
		return nil, err
	}
	yradius, err := c4Coordinate(r)
	if err != nil {
		return nil, err
	}
	items := []scene.Primitive{outer, &scene.Ellipse{Shape: shape, CX: cx, CY: cy, RX: xradius, RY: yradius}}
	if profile == scene.ProfileCell {
		items = append(items, &scene.SymbolRef{Symbol: "database", At: geom.Point{X: cx, Y: rect.Y}, Style: "node"})
	}
	return items, nil
}

func c4CylinderPath(rect geom.Rect, radius int64) (scene.Primitive, error) {
	left, top := int64(rect.X), int64(rect.Y)
	right, bottom := left+int64(rect.W), top+int64(rect.H)
	centre := left + int64(rect.W)/2
	dx, dy := int64(rect.W)*552/2000, radius*552/1000
	coordinates := [...][2]int64{
		{left, top + radius},
		{left, bottom - radius},
		{left, bottom - radius + dy},
		{centre - dx, bottom},
		{centre, bottom},
		{centre + dx, bottom},
		{right, bottom - radius + dy},
		{right, bottom - radius},
		{right, top + radius},
		{right, top + radius - dy},
		{centre + dx, top},
		{centre, top},
		{centre - dx, top},
		{left, top + radius - dy},
		{left, top + radius},
	}
	var points [15]geom.Point
	for i, p := range coordinates {
		x, err := c4Coordinate(p[0])
		if err != nil {
			return nil, err
		}
		y, err := c4Coordinate(p[1])
		if err != nil {
			return nil, err
		}
		points[i] = geom.Point{X: x, Y: y}
	}
	return &scene.Path{Shape: scene.Shape{Style: "node"}, Commands: []scene.Command{
		&scene.MoveTo{P: points[0]}, &scene.LineTo{P: points[1]},
		&scene.CubicTo{C1: points[2], C2: points[3], P: points[4]},
		&scene.CubicTo{C1: points[5], C2: points[6], P: points[7]},
		&scene.LineTo{P: points[8]},
		&scene.CubicTo{C1: points[9], C2: points[10], P: points[11]},
		&scene.CubicTo{C1: points[12], C2: points[13], P: points[14]},
		&scene.ClosePath{},
	}}, nil
}
