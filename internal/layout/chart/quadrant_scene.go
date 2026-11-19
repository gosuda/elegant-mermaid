package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func (p *quadPlan) textItem(i int) *scene.Text {
	role, size := p.styleOf(p.specs[i])
	style := "text"
	switch p.specs[i].kind {
	case quadXLeft, quadXRight, quadYBottom, quadYTop:
		style = "text-muted"
	}
	lines := make([][]scene.Run, len(p.texts[i].lines))
	for j, line := range p.texts[i].lines {
		for _, run := range line.Runs {
			lines[j] = append(lines[j], scene.Run{Text: run.Text, Bold: run.Bold, Italic: run.Italic})
		}
	}
	return &scene.Text{Rect: p.labelRects[i], Role: textRole(role), Size: size, Align: p.aligns[i], Style: style, Lines: lines}
}

func (p *quadPlan) textItems(owner string) []scene.Primitive {
	var items []scene.Primitive
	for i, s := range p.specs {
		if s.owner == owner {
			items = append(items, p.textItem(i))
		}
	}
	return items
}

func (p *quadPlan) divider(x0, y0, x1, y1 int64) (scene.Primitive, error) {
	from, err := pointOf(x0, y0)
	if err != nil {
		return nil, err
	}
	to, err := pointOf(x1, y1)
	if err != nil {
		return nil, err
	}
	return &scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{from, to}}, nil
}

func (p *quadPlan) plotItems() ([]scene.Primitive, error) {
	pl, e := p.plot, p.c.edge
	frame, err := pl.geom()
	if err != nil {
		return nil, err
	}
	items := []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "rule", Width: scene.Width{Kind: scene.WidthEmphasis}}, Rect: frame}}
	column, row := p.tiles[0].x, p.tiles[2].y
	for _, ends := range [][4]int64{{column, pl.y, column, pl.y + pl.h - e}, {pl.x, row, pl.x + pl.w - e, row}} {
		item, err := p.divider(ends[0], ends[1], ends[2], ends[3])
		if err != nil {
			return nil, err
		}
		items = append(items, item)
	}
	return append(items, p.textItems(plotID)...), nil
}

func (p *quadPlan) pointItems(k int) ([]scene.Primitive, error) {
	r := p.radii[k]
	var items []scene.Primitive
	if r.x > 0 && r.y > 0 {
		ellipse, err := p.pointEllipse(k)
		if err != nil {
			return nil, err
		}
		items = append(items, ellipse)
	}
	return append(items, p.textItems(pointBoxID(k))...), nil
}

func (p *quadPlan) pointEllipse(k int) (*scene.Ellipse, error) {
	c, r := p.centres[k], p.radii[k]
	cx, err := i32(c.x)
	if err != nil {
		return nil, err
	}
	cy, err := i32(c.y)
	if err != nil {
		return nil, err
	}
	rx, err := i32(r.x)
	if err != nil {
		return nil, err
	}
	ry, err := i32(r.y)
	if err != nil {
		return nil, err
	}
	return &scene.Ellipse{Shape: scene.Shape{Style: "series"}, CX: cx, CY: cy, RX: rx, RY: ry}, nil
}

func (p *quadPlan) boxItems(b quadBox) ([]scene.Primitive, error) {
	switch b.kind {
	case quadPlot:
		return p.plotItems()
	case quadTile:
		return p.textItems(b.id), nil
	}
	return p.pointItems(b.index)
}

func (p *quadPlan) groups() ([]*scene.Group, error) {
	bands := make([]scene.Primitive, tileCount)
	for i := range tileCount {
		g, err := p.tiles[i].geom()
		if err != nil {
			return nil, err
		}
		bands[i] = &scene.Rect{Shape: scene.Shape{Style: "band"}, Rect: g}
	}
	groups := []*scene.Group{{Role: scene.GroupRoleDecor, Items: bands}}
	for _, b := range p.boxes {
		items, err := p.boxItems(b)
		if err != nil {
			return nil, err
		}
		groups = append(groups, &scene.Group{Role: scene.GroupRoleNode, Owner: b.id, Items: items})
	}
	return groups, nil
}
