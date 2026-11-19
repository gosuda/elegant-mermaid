package lanes

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	journeyTitleSize = 16
	journeyTextSize  = 14
	journeySeriesMax = 12
	journeyHalfTurn  = 32768
)

func (pl *journeyPlanner) paint(f *frame, res JourneyResult) []*scene.Group {
	groups := make([]*scene.Group, 0, len(pl.in.Sections)+len(pl.in.Tasks)+1)
	for b, s := range pl.in.Sections {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleGroup, Owner: s.ID, Items: pl.bandItems(f, res, b)})
	}
	if t := pl.in.Title; t != nil {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: t.ID, Items: []scene.Primitive{pl.textItem(&t.Label, res.Title, "text")}})
	}
	for k, t := range pl.in.Tasks {
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: t.ID, Items: pl.taskItems(f, res, k)})
	}
	return groups
}

func (pl *journeyPlanner) card(shape scene.Shape, rect geom.Rect) scene.Primitive {
	return &scene.RoundRect{Shape: shape, Rect: rect, R: int32(pl.c.cornerRadius)}
}

func journeySeries(band int) scene.Shape {
	shape := plain("series-tint")
	shape.Series = uint8(band % journeySeriesMax)
	return shape
}

func (pl *journeyPlanner) bandItems(f *frame, res JourneyResult, b int) []scene.Primitive {
	shape := journeySeries(b)
	shape.Width = scene.Width{Kind: scene.WidthEmphasis}
	label := &pl.in.Sections[b].Label
	return []scene.Primitive{pl.card(shape, res.Bands[b]), pl.textItem(label, f.rect(pl.sections[b]), "text")}
}

func (pl *journeyPlanner) taskItems(f *frame, res JourneyResult, k int) []scene.Primitive {
	t := pl.in.Tasks[k]
	shape := plain("node")
	if t.Band != NoBand {
		shape = journeySeries(t.Band)
	}
	items := append([]scene.Primitive{pl.card(shape, res.Tasks[k])}, pl.face(res.Faces[k], t.Score)...)
	items = append(items, pl.textItem(&t.Label, f.rect(pl.names[k]), "text"))
	if t.People != nil {
		items = append(items, pl.textItem(t.People, f.rect(pl.people[k]), "text-muted"))
	}
	return items
}

func (pl *journeyPlanner) textItem(label *Text, rect geom.Rect, style string) scene.Primitive {
	size := int32(journeyTextSize)
	if label.Role == scene.TextRoleTitle {
		size = journeyTitleSize
	}
	return &scene.Text{Rect: rect, Role: label.Role, Size: size, Align: scene.AlignMiddle, Style: style, Lines: runs(label.Lines)}
}

func (pl *journeyPlanner) face(at geom.Point, score int) []scene.Primitive {
	if pl.isCell() {
		return []scene.Primitive{&scene.SymbolRef{Symbol: "ring", At: at, Style: "ink-line"}}
	}
	r := int64(pl.c.faceRadius)
	third, eye := int32(geom.FloorDiv(r, 3)), int32(max(geom.FloorDiv(r, 6), 1))
	items := []scene.Primitive{
		&scene.Ellipse{Shape: plain("ink-line"), CX: at.X, CY: at.Y, RX: int32(r), RY: int32(r)},
		&scene.Ellipse{Shape: plain("ink"), CX: at.X - third, CY: at.Y - third, RX: eye, RY: eye},
		&scene.Ellipse{Shape: plain("ink"), CX: at.X + third, CY: at.Y - third, RX: eye, RY: eye},
	}
	return append(items, pl.mouth(at, r, third, score))
}

func (pl *journeyPlanner) mouth(at geom.Point, r int64, third int32, score int) scene.Primitive {
	mid := int(half(pl.c.scoreMin + pl.c.scoreMax))
	radius := int32(geom.FloorDiv(r, 2))
	switch {
	case score > mid:
		return arcMouth(at.X, at.Y+int32(geom.FloorDiv(2*r, 15)), radius, journeyHalfTurn)
	case score < mid:
		return arcMouth(at.X, at.Y+int32(geom.FloorDiv(7*r, 15)), radius, -journeyHalfTurn)
	}
	y := at.Y + int32(geom.FloorDiv(7*r, 15))
	return &scene.Polyline{Shape: plain("ink-line"), Points: []geom.Point{{X: at.X - third, Y: y}, {X: at.X + third, Y: y}}}
}

func arcMouth(cx, cy, radius, sweep int32) scene.Primitive {
	return &scene.Path{Shape: plain("ink-line"), Commands: []scene.Command{
		&scene.MoveTo{P: geom.Point{X: cx + radius, Y: cy}},
		&scene.ArcTo{CX: cx, CY: cy, R: radius, A0: 0, Sweep: sweep},
	}}
}
