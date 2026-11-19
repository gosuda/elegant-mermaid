package chart

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type link struct {
	horizontal     bool
	x0, y0, x1, y1 int64
}

func (l link) ends() (from, to int64) {
	if l.horizontal {
		return l.x0, l.x1
	}
	return l.y0, l.y1
}

func (l link) path(mid int64) []curvePoint {
	if l.horizontal {
		return dedupe([]curvePoint{{l.x0, l.y0}, {mid, l.y0}, {mid, l.y1}, {l.x1, l.y1}})
	}
	return dedupe([]curvePoint{{l.x0, l.y0}, {l.x0, mid}, {l.x1, mid}, {l.x1, l.y1}})
}

func (l link) lanes(others []rect, gap int64) []int64 {
	from, to := l.ends()
	natural := geom.FloorDiv(from+to, 2)
	lo, hi := min(from, to), max(from, to)
	mids := []int64{natural}
	for _, o := range others {
		before, after := o.y-gap, o.bottom()+gap
		if l.horizontal {
			before, after = o.x-gap, o.right()+gap
		}
		for _, m := range [...]int64{before, after} {
			if m >= lo && m <= hi && !slices.Contains(mids, m) {
				mids = append(mids, m)
			}
		}
	}
	slices.SortFunc(mids[1:], func(a, b int64) int {
		return cmp.Or(cmp.Compare(absDelta(a-natural), absDelta(b-natural)), cmp.Compare(a, b))
	})
	return mids
}

func horizontalLink(a, b *domainPlan) (link, bool) {
	switch {
	case a.box.right() <= b.box.x:
		return link{true, a.box.right(), a.anchorY, b.box.x, b.anchorY}, true
	case b.box.right() <= a.box.x:
		return link{true, a.box.x, a.anchorY, b.box.right(), b.anchorY}, true
	}
	return link{}, false
}

func verticalLink(a, b *domainPlan) (link, bool) {
	switch {
	case a.box.bottom() <= b.box.y:
		return link{false, a.cx, a.box.bottom(), b.cx, b.box.y}, true
	case b.box.bottom() <= a.box.y:
		return link{false, a.cx, a.box.y, b.cx, b.box.bottom()}, true
	}
	return link{}, false
}

func links(a, b *domainPlan) []link {
	h, hok := horizontalLink(a, b)
	v, vok := verticalLink(a, b)
	switch {
	case hok && vok:
		return []link{h, v}
	case hok:
		return []link{h}
	case vok:
		return []link{v}
	case a.cx <= b.cx:
		return []link{{true, a.box.right(), a.anchorY, b.box.x, b.anchorY}}
	}
	return []link{{true, a.box.x, a.anchorY, b.box.right(), b.anchorY}}
}

func crosses(path []curvePoint, o rect) bool {
	for i := 1; i < len(path); i++ {
		a, b := path[i-1], path[i]
		if min(a.x, b.x) <= o.right() && max(a.x, b.x) >= o.x && min(a.y, b.y) <= o.bottom() && max(a.y, b.y) >= o.y {
			return true
		}
	}
	return false
}

func crossesAny(path []curvePoint, others []rect) bool {
	return slices.ContainsFunc(others, func(o rect) bool { return crosses(path, o) })
}

func overlaps(a, b rect) bool {
	return a.x < b.right() && b.x < a.right() && a.y < b.bottom() && b.y < a.bottom()
}

func hitsLabel(path []curvePoint, at rect, reach int64) bool {
	for i := 1; i < len(path); i++ {
		a, b := path[i-1], path[i]
		if min(a.x, b.x) < at.right() && max(a.x, b.x)+reach > at.x && min(a.y, b.y) < at.bottom() && max(a.y, b.y)+reach > at.y {
			return true
		}
	}
	return false
}
