package lanes

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type cardKind uint8

const (
	cardSection cardKind = iota
	cardPeriod
	cardEvent
)

const (
	titleSize = 16
	textSize  = 14
	seriesMax = 12
)

func (pl *timelinePlanner) series(period int) uint8 {
	section := pl.in.Periods[period].Section
	switch {
	case len(pl.in.Sections) == 0:
		return uint8(period % seriesMax)
	case section == NoSection:
		return 0
	}
	return uint8(section % seriesMax)
}

func (pl *timelinePlanner) paint(f *frame, res TimelineResult) []*scene.Group {
	groups := []*scene.Group{pl.axisGroup(f)}
	for i, p := range pl.in.Periods {
		for k, e := range p.Events {
			groups = append(groups, &scene.Group{Role: scene.GroupRoleEdge, Owner: e.Link, Items: pl.linkItems(res.Routes[i][k])})
		}
	}
	if t := pl.in.Title; t != nil {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: t.ID, Items: []scene.Primitive{pl.textItem(&t.Label, res.Title)}})
	}
	for s, section := range pl.in.Sections {
		series := uint8(s % seriesMax)
		groups = append(groups, pl.card(section.ID, cardSection, series, &section.Label, res.Sections[s]))
	}
	for i, p := range pl.in.Periods {
		groups = append(groups, pl.card(p.ID, cardPeriod, pl.series(i), &p.Label, res.Periods[i]))
		for k, e := range p.Events {
			groups = append(groups, pl.card(e.ID, cardEvent, 0, &e.Label, res.Events[i][k]))
		}
	}
	return groups
}

func (pl *timelinePlanner) axisGroup(f *frame) *scene.Group {
	line := plain("edge")
	line.Width = scene.Width{Kind: scene.WidthEmphasis}
	end := f.point(pl.axis[1])
	direction := scene.AxisPlusX
	if pl.vertical() {
		direction = scene.AxisPlusY
	}
	return &scene.Group{Role: scene.GroupRoleDecor, Items: []scene.Primitive{
		&scene.Polyline{Shape: line, Points: []geom.Point{f.point(pl.axis[0]), end}},
		&scene.MarkerRef{Marker: "point", At: end, Axis: direction},
	}}
}

func (pl *timelinePlanner) linkItems(route []geom.Point) []scene.Primitive {
	shape := plain("edge")
	shape.Line = scene.LineDotted
	return []scene.Primitive{&scene.Polyline{Shape: shape, Corner: int32(pl.c.cornerRadius), Points: route}}
}

func (pl *timelinePlanner) card(id string, kind cardKind, series uint8, label *Text, rect geom.Rect) *scene.Group {
	return &scene.Group{Role: scene.GroupRoleNode, Owner: id, Items: []scene.Primitive{
		pl.cardShape(kind, series, rect),
		pl.textItem(label, pl.textRect(label, rect)),
	}}
}

func (pl *timelinePlanner) cardShape(kind cardKind, series uint8, rect geom.Rect) scene.Primitive {
	shape := plain("node")
	if kind != cardEvent {
		shape = plain("series-tint")
		shape.Series = series
	}
	if kind == cardSection {
		shape.Width = scene.Width{Kind: scene.WidthEmphasis}
	}
	if pl.isCell() && kind != cardPeriod {
		return &scene.Rect{Shape: shape, Rect: rect}
	}
	return &scene.RoundRect{Shape: shape, Rect: rect, R: int32(pl.c.cornerRadius)}
}

func (pl *timelinePlanner) textRect(label *Text, card geom.Rect) geom.Rect {
	n := int64(len(label.Lines))
	h := n * (int64(label.H) / max(n, 1))
	return geom.Rect{X: card.X, Y: card.Y + int32(half(int64(card.H)-h)), W: card.W, H: int32(h)}
}

func (pl *timelinePlanner) textItem(label *Text, rect geom.Rect) scene.Primitive {
	size := int32(textSize)
	if label.Role == scene.TextRoleTitle {
		size = titleSize
	}
	return &scene.Text{Rect: rect, Role: label.Role, Size: size, Align: scene.AlignMiddle, Style: "text", Lines: runs(label.Lines)}
}
