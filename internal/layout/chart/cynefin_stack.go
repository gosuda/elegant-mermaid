package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type curvePoint struct{ x, y int64 }

type domainPlan struct {
	name    string
	title   textBox
	items   []textBox
	cx      int64
	nameAt  rect
	badges  []rect
	texts   []rect
	box     rect
	anchorY int64
}

func (r rect) right() int64  { return r.x + r.w }
func (r rect) bottom() int64 { return r.y + r.h }

func (d *domainPlan) widest(c cynefinConsts) int64 {
	widest := d.title.w
	for _, item := range d.items {
		widest = max(widest, item.w+2*c.itemPadX)
	}
	return widest
}

func (d *domainPlan) height(c cynefinConsts) int64 {
	total := d.title.h
	for i, item := range d.items {
		if i == 0 {
			total += c.nameGap
		} else {
			total += c.itemGap
		}
		total += item.h + 2*c.itemPadY
	}
	return total
}

func (d *domainPlan) span(c cynefinConsts) (lo, hi int64) {
	widest := d.widest(c)
	lo = geom.FloorDiv(widest, 2) + c.boxPad
	return lo, widest - geom.FloorDiv(widest, 2) + c.boxPad
}

func (d *domainPlan) place(c cynefinConsts, cx, top int64) {
	d.cx = cx
	d.nameAt = rect{cx - geom.FloorDiv(d.title.w, 2), top, d.title.w, d.title.h}
	d.anchorY = top + geom.FloorDiv(d.title.h, 2)
	d.badges, d.texts = nil, nil
	y := top + d.title.h + c.nameGap
	for _, item := range d.items {
		badgeW, badgeH := item.w+2*c.itemPadX, item.h+2*c.itemPadY
		d.badges = append(d.badges, rect{cx - geom.FloorDiv(badgeW, 2), y, badgeW, badgeH})
		d.texts = append(d.texts, rect{cx - geom.FloorDiv(item.w, 2), y + c.itemPadY, item.w, item.h})
		y += badgeH + c.itemGap
	}
	d.box = d.bounds(c)
}

func (d *domainPlan) bounds(c cynefinConsts) rect {
	x0, y0, x1, y1 := d.nameAt.x, d.nameAt.y, d.nameAt.right(), d.nameAt.bottom()
	for _, b := range d.badges {
		x0, y0, x1, y1 = min(x0, b.x), min(y0, b.y), max(x1, b.right()), max(y1, b.bottom())
	}
	return rect{x0 - c.boxPad, y0 - c.boxPad, x1 - x0 + 2*c.boxPad, y1 - y0 + 2*c.boxPad}
}
