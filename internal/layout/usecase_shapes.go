package layout

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type usecaseShapeSpec struct {
	id       string
	business bool
	hasIcon  bool
	pkg      bool
}

func parseUsecaseShape(encoded string) usecaseShapeSpec {
	id, flag, _ := strings.Cut(encoded, ":")
	return usecaseShapeSpec{
		id:       id,
		business: flag == "business" || strings.HasPrefix(flag, "business:"),
		hasIcon:  id == "usecaseActorIcon",
		pkg:      flag == "package",
	}
}

func (s usecaseShapeSpec) isActor() bool { return strings.HasPrefix(s.id, "usecaseActor") }

func usecaseTexts(items []scene.Primitive) []*scene.Text {
	var texts []*scene.Text
	for _, item := range items {
		if text, ok := item.(*scene.Text); ok {
			texts = append(texts, text)
		}
	}
	return texts
}

func usecaseRecordLabelRect(s *scene.Scene, owner string, rect geom.Rect) {
	for i := range s.Labels {
		if s.Labels[i].Owner == owner {
			s.Labels[i].Rect = rect
		}
	}
}

func usecaseDrawGroup(in Input, s *scene.Scene, group *scene.Group) error {
	box := usecaseFindBox(in.Boxes, group.Owner)
	bounds := usecaseSceneBox(s, group.Owner)
	if box == nil || bounds == nil {
		return nil
	}
	spec := parseUsecaseShape(box.Shape)
	texts := usecaseTexts(group.Items)
	if spec.isActor() {
		if err := usecasePositionCaption(texts, bounds.Rect, in.Profile); err != nil {
			return err
		}
	}
	if len(texts) > 0 {
		usecaseRecordLabelRect(s, group.Owner, texts[0].Rect)
	}
	items, err := usecaseOutline(spec, bounds, in.Profile)
	if err != nil {
		return err
	}
	for _, text := range texts {
		items = append(items, text)
	}
	group.Items = items
	return nil
}

func usecaseDrawShapes(in Input, s *scene.Scene) error {
	for _, group := range s.Groups {
		if err := usecaseDrawGroup(in, s, group); err != nil {
			return err
		}
	}
	return nil
}

func usecaseFindBox(boxes []Box, id string) *Box {
	for i := range boxes {
		if boxes[i].ID == id {
			return &boxes[i]
		}
	}
	return nil
}

func usecaseSceneBox(s *scene.Scene, id string) *scene.Box {
	for i := range s.Boxes {
		if s.Boxes[i].ID == id {
			return &s.Boxes[i]
		}
	}
	return nil
}

func usecasePositionCaption(texts []*scene.Text, rect geom.Rect, profile scene.Profile) error {
	top, padding := int64(88*64), int64(8*64)
	if profile == scene.ProfileCell {
		top, padding = 7, 1
	}
	for _, text := range texts {
		y, err := usecaseInt32(int64(rect.Y) + top)
		if err != nil {
			return err
		}
		x, err := usecaseInt32(int64(rect.X) + padding)
		if err != nil {
			return err
		}
		w, err := usecaseInt32(int64(rect.W) - 2*padding)
		if err != nil {
			return err
		}
		text.Rect.X, text.Rect.Y, text.Rect.W = x, y, w
	}
	return nil
}

func usecaseOutline(spec usecaseShapeSpec, bounds *scene.Box, profile scene.Profile) ([]scene.Primitive, error) {
	rect := bounds.Rect
	if spec.isActor() {
		drawing, err := newUsecaseActor(rect, profile)
		if err != nil {
			return nil, err
		}
		return drawing.items(spec)
	}
	style := "node"
	switch {
	case bounds.Role == scene.RoleGroup:
		style = "group"
	case spec.id == "note":
		style = "note"
	}
	if spec.id == "usecaseEllipse" || spec.id == "usecaseBusiness" {
		return usecaseEllipseItems(spec.id, rect, style)
	}
	items := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: style}, Rect: rect}}
	if spec.pkg {
		tab := geom.Rect{X: rect.X, Y: rect.Y, W: rect.W / 3, H: usecaseConstant(profile, "line_h")}
		items = append(items, &scene.Rect{Shape: scene.Shape{Style: style}, Rect: tab})
	}
	return items, nil
}

func usecaseOffset(origin, delta int32) (int32, error) {
	return usecaseInt32(int64(origin) + int64(delta))
}

func usecaseEllipseItems(id string, rect geom.Rect, style string) ([]scene.Primitive, error) {
	cx, err := usecaseOffset(rect.X, rect.W/2)
	if err != nil {
		return nil, err
	}
	cy, err := usecaseOffset(rect.Y, rect.H/2)
	if err != nil {
		return nil, err
	}
	items := []scene.Primitive{&scene.Ellipse{Shape: scene.Shape{Style: style}, CX: cx, CY: cy, RX: rect.W / 2, RY: rect.H / 2}}
	if id != "usecaseBusiness" {
		return items, nil
	}
	ax, err := usecaseOffset(cx, rect.W/3)
	if err != nil {
		return nil, err
	}
	ay, err := usecaseOffset(cy, rect.H/4)
	if err != nil {
		return nil, err
	}
	bx, err := usecaseOffset(cx, rect.W/2)
	if err != nil {
		return nil, err
	}
	by, err := usecaseOffset(cy, -(rect.H / 4))
	if err != nil {
		return nil, err
	}
	return append(items, &scene.Polyline{Shape: scene.Shape{Style: style}, Points: []geom.Point{{X: ax, Y: ay}, {X: bx, Y: by}}}), nil
}

type usecaseActor struct {
	origin  geom.Point
	profile scene.Profile
}

type usecasePath [][2]int32

func newUsecaseActor(rect geom.Rect, profile scene.Profile) (usecaseActor, error) {
	x, err := usecaseOffset(rect.X, rect.W/2)
	if err != nil {
		return usecaseActor{}, err
	}
	top := int32(8 * 64)
	if profile == scene.ProfileCell {
		top = 1
	}
	y, err := usecaseOffset(rect.Y, top)
	return usecaseActor{origin: geom.Point{X: x, Y: y}, profile: profile}, err
}

func (a usecaseActor) point(x, y int32) (geom.Point, error) {
	dx, dy := int64(x)*64, (int64(y)+36)*64
	if a.profile == scene.ProfileCell {
		dx, dy = geom.FloorDiv(int64(x)*7, 56), geom.FloorDiv((int64(y)+36)*5, 72)
	}
	px, err := usecaseInt32(int64(a.origin.X) + dx)
	if err != nil {
		return geom.Point{}, err
	}
	py, err := usecaseInt32(int64(a.origin.Y) + dy)
	return geom.Point{X: px, Y: py}, err
}

func (a usecaseActor) points(path usecasePath) ([]geom.Point, error) {
	points := make([]geom.Point, len(path))
	for i, p := range path {
		var err error
		if points[i], err = a.point(p[0], p[1]); err != nil {
			return nil, err
		}
	}
	return points, nil
}

func (a usecaseActor) items(spec usecaseShapeSpec) ([]scene.Primitive, error) {
	if spec.hasIcon {
		return a.iconItems(spec)
	}
	y, radius := int32(-24), int32(12)
	switch spec.id {
	case "usecaseActorHollow":
		y, radius = -23, 9
	case "usecaseActorAwesome":
		y, radius = -21, 13
	}
	center, err := a.point(0, y)
	if err != nil {
		return nil, err
	}
	items := []scene.Primitive{a.head(center, radius)}
	body, err := a.body(spec.id)
	if err != nil {
		return nil, err
	}
	items = append(items, body...)
	if spec.business {
		slash, err := a.stroke(usecasePath{{3, y + radius}, {radius, y - radius}})
		if err != nil {
			return nil, err
		}
		items = append(items, slash)
	}
	return items, nil
}

func (a usecaseActor) body(id string) ([]scene.Primitive, error) {
	switch id {
	case "usecaseActorHollow":
		points, err := a.points(usecasePath{{-22, -10}, {22, -10}, {22, 0}, {6, 0}, {22, 17}, {13, 28}, {0, 13}, {-13, 28}, {-22, 17}, {-6, 0}, {-22, 0}})
		return []scene.Primitive{&scene.Polygon{Shape: scene.Shape{Style: "ink-line"}, Points: points}}, err
	case "usecaseActorAwesome":
		silhouette, err := a.silhouette()
		return []scene.Primitive{silhouette}, err
	}
	var items []scene.Primitive
	for _, path := range [...]usecasePath{{{0, -12}, {0, 8}}, {{-17, -5}, {17, -5}}, {{-15, 28}, {0, 8}, {15, 28}}} {
		stroke, err := a.stroke(path)
		if err != nil {
			return nil, err
		}
		items = append(items, stroke)
	}
	return items, nil
}

func (a usecaseActor) head(center geom.Point, radius int32) scene.Primitive {
	rx, ry := radius*64, radius*64
	if a.profile == scene.ProfileCell {
		rx, ry = 1, 1
	}
	return &scene.Ellipse{Shape: scene.Shape{Style: "ink-line"}, CX: center.X, CY: center.Y, RX: rx, RY: ry}
}

func (a usecaseActor) stroke(path usecasePath) (scene.Primitive, error) {
	points, err := a.points(path)
	return &scene.Polyline{Shape: scene.Shape{Style: "ink-line"}, Points: points}, err
}

func (a usecaseActor) silhouette() (scene.Primitive, error) {
	p, err := a.points(usecasePath{{-24, 25}, {-24, 7}, {-14, -3}, {0, -3}, {14, -3}, {24, 7}, {24, 25}, {18, 30}, {-18, 30}})
	if err != nil {
		return nil, err
	}
	return &scene.Path{Shape: scene.Shape{Style: "ink-line"}, Commands: []scene.Command{
		&scene.MoveTo{P: p[0]},
		&scene.CubicTo{C1: p[1], C2: p[2], P: p[3]},
		&scene.CubicTo{C1: p[4], C2: p[5], P: p[6]},
		&scene.LineTo{P: p[7]},
		&scene.LineTo{P: p[8]},
		&scene.ClosePath{},
	}}, nil
}

func (a usecaseActor) iconItems(spec usecaseShapeSpec) ([]scene.Primitive, error) {
	corners, err := a.points(usecasePath{{-26, -28}, {26, 24}, {0, -2}})
	if err != nil {
		return nil, err
	}
	top, end, center := corners[0], corners[1], corners[2]
	rect := geom.Rect{X: top.X, Y: top.Y, W: end.X - top.X, H: end.Y - top.Y}
	frame := &scene.RoundRect{Shape: scene.Shape{Style: "ink-line"}, Rect: rect}
	var glyph scene.Primitive
	if a.profile == scene.ProfileCell {
		glyph = &scene.SymbolRef{Symbol: "unknown", At: center, Style: "ink-line"}
	} else {
		frame.R = 4 * 64
		glyph = &scene.Text{Rect: rect, Role: scene.TextRoleLabel, Size: 24, Align: scene.AlignMiddle, Style: "text", Lines: [][]scene.Run{{{Text: "?"}}}}
	}
	items := []scene.Primitive{frame, glyph}
	if !spec.business {
		return items, nil
	}
	slash, err := a.stroke(usecasePath{{12, -8}, {26, -26}})
	return append([]scene.Primitive{slash}, items...), err
}
