package lanes

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type eventShift struct {
	dx, dy int64
	err    error
}

func (s *eventShift) fit(v int64) int32 {
	if abs64(v) > geom.CoordLimit {
		s.err = geom.ErrOverflow
		return 0
	}
	return int32(v)
}

func (s *eventShift) point(p eventPoint) geom.Point {
	return geom.Point{X: s.fit(p.x + s.dx), Y: s.fit(p.y + s.dy)}
}

func (s *eventShift) rect(b eventBox) geom.Rect {
	return geom.Rect{X: s.fit(b.x + s.dx), Y: s.fit(b.y + s.dy), W: s.fit(b.w), H: s.fit(b.h)}
}

func eventUnion(a, b eventBox) eventBox {
	x, y := min(a.x, b.x), min(a.y, b.y)
	return eventBox{x: x, y: y, w: max(a.x+a.w, b.x+b.w) - x, h: max(a.bottom(), b.bottom()) - y}
}

func (pl *eventPlanner) laneBox(lane int) eventBox {
	return eventBox{x: 0, y: pl.laneY[lane], w: pl.maxR + pl.c.lanePadding, h: pl.laneH[lane]}
}

func (pl *eventPlanner) labelBox(lane int) eventBox {
	label := pl.in.Lanes[lane].Label
	if label == nil {
		return eventBox{}
	}
	return eventBox{x: pl.c.labelInset(), y: pl.laneY[lane] + pl.c.lanePadding, w: int64(label.W), h: int64(label.H)}
}

func (pl *eventPlanner) frameTexts(i int) (name, data eventBox) {
	frame, box := pl.in.Frames[i], pl.frames[i]
	areaX, areaY := box.x+pl.c.boxPadding, box.y+pl.c.boxPadding
	areaW, areaH := box.w-2*pl.c.boxPadding, box.h-2*pl.c.boxPadding
	nameH := int64(frame.Name.H)
	total := nameH
	if frame.Data != nil {
		total += pl.c.lineHeight + int64(frame.Data.H)
	}
	top := areaY + max(0, geom.FloorDiv(areaH-total, 2))
	name = eventBox{x: areaX, y: top, w: areaW, h: nameH}
	if frame.Data != nil {
		data = eventBox{x: areaX, y: top + nameH + pl.c.lineHeight, w: areaW, h: int64(frame.Data.H)}
	}
	return name, data
}

func (pl *eventPlanner) extent() eventBox {
	var extent eventBox
	for lane := range pl.in.Lanes {
		extent = eventUnion(extent, pl.laneBox(lane))
		extent = eventUnion(extent, pl.labelBox(lane))
	}
	for i := range pl.in.Frames {
		name, data := pl.frameTexts(i)
		extent = eventUnion(eventUnion(eventUnion(extent, pl.frames[i]), name), data)
	}
	for _, route := range pl.routes {
		for _, p := range route {
			extent = eventUnion(extent, eventBox{x: p.x, y: p.y})
		}
	}
	return extent
}

func (pl *eventPlanner) result() (EventModelingResult, error) {
	extent := pl.extent()
	s := &eventShift{dx: pl.c.canvasMargin - extent.x, dy: pl.c.canvasMargin - extent.y}
	res := EventModelingResult{Canvas: geom.Size{W: s.fit(extent.w + 2*pl.c.canvasMargin), H: s.fit(extent.h + 2*pl.c.canvasMargin)}}
	for lane := range pl.in.Lanes {
		res.Lanes = append(res.Lanes, s.rect(pl.laneBox(lane)))
		res.LaneLabels = append(res.LaneLabels, s.rect(pl.labelBox(lane)))
	}
	for i := range pl.in.Frames {
		res.Frames = append(res.Frames, s.rect(pl.frames[i]))
	}
	for _, route := range pl.routes {
		points := make([]geom.Point, len(route))
		for i, p := range route {
			points[i] = s.point(p)
		}
		res.Routes = append(res.Routes, points)
	}
	if s.err != nil {
		return EventModelingResult{}, s.err
	}
	res.Groups = pl.paint(s, res)
	return res, s.err
}

func eventRuns(lines []measure.StyledLine) [][]scene.Run {
	out := make([][]scene.Run, len(lines))
	for i, line := range lines {
		out[i] = make([]scene.Run, len(line.Runs))
		for j, run := range line.Runs {
			out[i][j] = scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic}
		}
	}
	return out
}

func eventText(text *Text, rect geom.Rect, align scene.Align) scene.Primitive {
	return &scene.Text{Rect: rect, Role: text.Role, Size: 14, Align: align, Style: "text", Lines: eventRuns(text.Lines)}
}

func eventStyle(category string) string {
	switch category {
	case "command":
		return "note"
	case "readmodel":
		return "success"
	case "event":
		return "warning"
	case "processor":
		return "mark-hollow"
	}
	return "node"
}

func eventAxis(a, b geom.Point) scene.Axis {
	dx, dy := int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y)
	if abs64(dx) >= abs64(dy) {
		if dx < 0 {
			return scene.AxisMinusX
		}
		return scene.AxisPlusX
	}
	if dy < 0 {
		return scene.AxisMinusY
	}
	return scene.AxisPlusY
}

func (pl *eventPlanner) paint(s *eventShift, res EventModelingResult) []*scene.Group {
	groups := make([]*scene.Group, 0, len(pl.in.Lanes)+len(pl.in.Relations)+len(pl.in.Frames))
	for lane, in := range pl.in.Lanes {
		if in.ID != "" {
			groups = append(groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: in.ID, Items: pl.laneItems(lane, res)})
		}
	}
	for i, relation := range pl.in.Relations {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: relation.ID, Items: pl.edgeItems(res.Routes[i])})
	}
	for i, frame := range pl.in.Frames {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: frame.ID, Items: pl.frameItems(s, res, i)})
	}
	return groups
}

func (pl *eventPlanner) laneItems(lane int, res EventModelingResult) []scene.Primitive {
	var items []scene.Primitive
	if pl.profile == scene.ProfileVector {
		items = append(items, &scene.Rect{Shape: scene.Shape{Style: "band"}, Rect: res.Lanes[lane]})
	}
	items = append(items, &scene.Rect{Shape: scene.Shape{Style: "group"}, Rect: res.Lanes[lane]})
	if label := pl.in.Lanes[lane].Label; label != nil {
		items = append(items, eventText(label, res.LaneLabels[lane], scene.AlignStart))
	}
	return items
}

func (pl *eventPlanner) edgeItems(points []geom.Point) []scene.Primitive {
	items := []scene.Primitive{&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Corner: int32(pl.c.cornerRadius), Points: points}}
	if end := len(points) - 1; end > 0 {
		items = append(items, &scene.MarkerRef{Marker: "point", At: points[end], Axis: eventAxis(points[end-1], points[end])})
	}
	return items
}

func (pl *eventPlanner) frameItems(s *eventShift, res EventModelingResult, i int) []scene.Primitive {
	frame := pl.in.Frames[i]
	items := []scene.Primitive{&scene.RoundRect{Shape: scene.Shape{Style: eventStyle(frame.Category)}, Rect: res.Frames[i], R: int32(pl.c.cornerRadius)}}
	name, data := pl.frameTexts(i)
	items = append(items, eventText(&frame.Name, s.rect(name), scene.AlignMiddle))
	if frame.Data != nil {
		items = append(items, eventText(frame.Data, s.rect(data), scene.AlignStart))
	}
	return items
}
