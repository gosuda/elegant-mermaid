package grid

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func (b *builder) connect(canvas *geom.Rect) ([][]geom.Point, []geom.Rect, error) {
	routes, err := b.route()
	if err != nil {
		return nil, nil, err
	}
	labels, err := b.placeLabels(routes, canvas)
	return routes, labels, err
}

type labelSite struct {
	routes [][]geom.Point
	leaves []geom.Rect
	frames []geom.Rect
	placed []geom.Rect
	canvas geom.Rect
}

func (b *builder) placeLabels(routes [][]geom.Point, canvas *geom.Rect) ([]geom.Rect, error) {
	labels := make([]geom.Rect, len(routes))
	site := &labelSite{routes: routes, leaves: b.leaves(), frames: b.frames(), canvas: *canvas}
	margin := max(int64(b.p.Padding), 1)
	spillX, spillY := int64(canvas.W)+margin, margin
	for k, e := range b.in.Edges {
		if e.Label.W == 0 && e.Label.H == 0 {
			continue
		}
		rect, ok := b.fitLabel(site, routes[k], e.Label)
		if !ok {
			if spillX+int64(e.Label.W)+margin > geom.CoordLimit || spillY+int64(e.Label.H)+margin > geom.CoordLimit {
				return nil, geom.ErrOverflow
			}
			rect = geom.Rect{X: int32(spillX), Y: int32(spillY), W: e.Label.W, H: e.Label.H}
			spillY += int64(e.Label.H) + margin
			canvas.W = max(canvas.W, int32(int64(rect.X)+int64(rect.W)+margin))
			canvas.H = max(canvas.H, int32(spillY))
			site.canvas = *canvas
		}
		labels[k] = rect
		site.placed = append(site.placed, rect)
	}
	return labels, nil
}

func (b *builder) fitLabel(site *labelSite, route []geom.Point, size geom.Size) (geom.Rect, bool) {
	for _, candidate := range b.candidates(route, size) {
		if b.vacant(site, candidate) {
			return candidate, true
		}
	}
	return geom.Rect{}, false
}

func (b *builder) candidates(route []geom.Point, size geom.Size) []geom.Rect {
	order := make([]int, 0, len(route))
	for i := 0; i+1 < len(route); i++ {
		if manhattan(route[i], route[i+1]) > 0 {
			order = append(order, i)
		}
	}
	slices.SortStableFunc(order, func(i, j int) int {
		return cmp.Compare(manhattan(route[j], route[j+1]), manhattan(route[i], route[i+1]))
	})
	var out []geom.Rect
	for _, i := range order {
		out = append(out, b.beside(route[i], route[i+1], size)...)
	}
	return out
}

func (b *builder) beside(from, to geom.Point, size geom.Size) []geom.Rect {
	mx, my := (int64(from.X)+int64(to.X))/2, (int64(from.Y)+int64(to.Y))/2
	w, h := int64(size.W), int64(size.H)
	off, thick := int64(b.p.Padding)/2, int64(b.p.LineThickness)
	if from.Y == to.Y {
		return []geom.Rect{rectOf(mx-w/2, my-off-h, w, h), rectOf(mx-w/2, my+thick+off, w, h)}
	}
	return []geom.Rect{rectOf(mx+thick+off, my-h/2, w, h), rectOf(mx-off-w, my-h/2, w, h)}
}

func rectOf(x, y, w, h int64) geom.Rect {
	return geom.Rect{X: int32(x), Y: int32(y), W: int32(w), H: int32(h)}
}

func overlaps(a, b geom.Rect) bool {
	return a.X < b.X+b.W && b.X < a.X+a.W && a.Y < b.Y+b.H && b.Y < a.Y+a.H
}

func strictlyInside(outer, inner geom.Rect) bool {
	return outer.X < inner.X && int64(inner.X)+int64(inner.W) < int64(outer.X)+int64(outer.W) &&
		outer.Y < inner.Y && int64(inner.Y)+int64(inner.H) < int64(outer.Y)+int64(outer.H)
}

func (b *builder) frames() []geom.Rect {
	var rects []geom.Rect
	for i, box := range b.in.Boxes {
		if box.Kind == KindComposite {
			rects = append(rects, b.rects[i])
		}
	}
	return rects
}

func (b *builder) vacant(site *labelSite, r geom.Rect) bool {
	if !strictlyInside(site.canvas, r) {
		return false
	}
	for _, frame := range site.frames {
		if overlaps(frame, r) && !strictlyInside(frame, r) {
			return false
		}
	}
	for _, others := range [][]geom.Rect{site.leaves, site.placed} {
		if slices.ContainsFunc(others, func(o geom.Rect) bool { return overlaps(r, o) }) {
			return false
		}
	}
	thick := b.p.LineThickness
	for _, route := range site.routes {
		for i := 0; i+1 < len(route); i++ {
			if segmentTouches(route[i], route[i+1], thick, r) {
				return false
			}
		}
	}
	return true
}

func segmentTouches(a, b geom.Point, thick int32, r geom.Rect) bool {
	x0, x1 := min(a.X, b.X), max(a.X, b.X)+thick
	y0, y1 := min(a.Y, b.Y), max(a.Y, b.Y)+thick
	return x0 < r.X+r.W && r.X < x1 && y0 < r.Y+r.H && r.Y < y1
}
