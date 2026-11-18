package chart

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func dedupe(points []curvePoint) []curvePoint {
	out := points[:1]
	for _, p := range points[1:] {
		if p != out[len(out)-1] {
			out = append(out, p)
		}
	}
	return out
}

func (p *cynefinPlan) elbow(a, b *domainPlan) []curvePoint {
	var others []rect
	for i := range p.domains {
		if d := &p.domains[i]; d != a && d != b {
			others = append(others, d.box)
		}
	}
	var first []curvePoint
	for _, l := range links(a, b) {
		for _, mid := range l.lanes(others, p.c.pad) {
			path := l.path(mid)
			if first == nil {
				first = path
			}
			if !crossesAny(path, others) {
				return path
			}
		}
	}
	return first
}

func (p *cynefinPlan) route() {
	p.paths = p.paths[:0]
	for _, r := range p.routes {
		p.paths = append(p.paths, p.elbow(p.domain(r.from), p.domain(r.to)))
	}
	for i, r := range p.routes {
		if r.label != "" {
			p.routeLabel(i, p.paths[i])
		}
	}
}

func absDelta(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func (p *cynefinPlan) labelBlocked(at rect) bool {
	for i := range p.domains {
		if overlaps(at, p.domains[i].box) {
			return true
		}
	}
	reach := p.pathReach()
	for _, path := range p.paths {
		if hitsLabel(path, at, reach) {
			return true
		}
	}
	return slices.ContainsFunc(p.extents, func(o rect) bool { return overlaps(at, o) })
}

type labelSegment struct{ a, b curvePoint }

func (p *cynefinPlan) pathReach() int64 {
	if p.profile == scene.ProfileCell {
		return 1
	}
	return 0
}

func segmentsByLength(path []curvePoint) []labelSegment {
	segs := make([]labelSegment, len(path))
	for i, pt := range path {
		segs[i] = labelSegment{path[max(i-1, 0)], pt}
	}
	length := func(s labelSegment) int64 { return absDelta(s.b.x-s.a.x) + absDelta(s.b.y-s.a.y) }
	slices.SortStableFunc(segs, func(x, y labelSegment) int { return cmp.Compare(length(y), length(x)) })
	return segs
}

func (p *cynefinPlan) labelSides(box textBox, s labelSegment) []placedLabel {
	mx, my := geom.FloorDiv(s.a.x+s.b.x, 2), geom.FloorDiv(s.a.y+s.b.y, 2)
	gap := p.c.labelGap
	if s.a.y != s.b.y {
		return []placedLabel{
			{at: rect{mx + gap, my - geom.FloorDiv(box.h, 2), box.w, box.h}, align: scene.AlignStart},
			{at: rect{mx - gap - box.w, my - geom.FloorDiv(box.h, 2), box.w, box.h}, align: scene.AlignStart},
		}
	}
	return []placedLabel{
		{at: rect{mx - geom.FloorDiv(box.w, 2), my + gap, box.w, box.h}, align: scene.AlignMiddle},
		{at: rect{mx - geom.FloorDiv(box.w, 2), my - gap - box.h, box.w, box.h}, align: scene.AlignMiddle},
	}
}

func (p *cynefinPlan) routeLabel(index int, path []curvePoint) {
	box := p.routeBoxes[index]
	var sides []placedLabel
	for _, s := range segmentsByLength(path) {
		sides = append(sides, p.labelSides(box, s)...)
	}
	for i := range sides {
		sides[i].at.x, sides[i].at.y = max(sides[i].at.x, 0), max(sides[i].at.y, 0)
	}
	chosen := sides[0]
	if i := slices.IndexFunc(sides, func(s placedLabel) bool { return !p.labelBlocked(s.at) }); i >= 0 {
		chosen = sides[i]
	}
	p.setLabel(routeLabelID(index), chosen.at, chosen.align, box)
}

func (p *cynefinPlan) setLabel(id string, at rect, align scene.Align, box textBox) {
	p.labels[id] = placedLabel{at: at, align: align, box: box}
	p.extents = append(p.extents, at)
}

func axisOf(a, b curvePoint) scene.Axis {
	dx, dy := b.x-a.x, b.y-a.y
	if absDelta(dx) >= absDelta(dy) {
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
