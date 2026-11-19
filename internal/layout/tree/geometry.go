package tree

import "github.com/gosuda/elegant-mermaid/internal/geom"

type placement struct {
	left  []int64
	y     []int64
	right []bool
}

func (p *placer) layout() (Layout, error) {
	at := p.positions()
	out := Layout{Boxes: make([]geom.Rect, len(p.nodes)), Routes: make([][]geom.Point, len(p.nodes))}
	for i, node := range p.nodes {
		top := at.y[i] - geom.FloorDiv(int64(node.Height), 2)
		box, ok := rect(at.left[i], top, int64(node.Width), int64(node.Height))
		if !ok {
			return Layout{}, geom.ErrOverflow
		}
		out.Boxes[i] = box
	}
	for i := 1; i < len(p.nodes); i++ {
		parent := p.nodes[i].Parent
		ends := [2]int64{at.y[parent], at.y[i]}
		if at.right[i] {
			out.Routes[i] = p.routeRight(out.Boxes[parent], out.Boxes[i], ends)
		} else {
			out.Routes[i] = p.routeLeft(out.Boxes[parent], out.Boxes[i], ends)
		}
	}
	return out, nil
}

func (p *placer) positions() placement {
	n := len(p.nodes)
	at := placement{left: make([]int64, n), y: make([]int64, n), right: make([]bool, n)}
	at.left[0] = -geom.FloorDiv(int64(p.nodes[0].Width), 2)
	rootChildren := 0
	for i := 1; i < n; i++ {
		parent := p.nodes[i].Parent
		at.right[i] = at.right[parent]
		if parent == 0 {
			at.right[i] = rootChildren%2 == 0
			rootChildren++
		}
		at.y[i] = at.y[parent] + p.dy[i]
		at.left[i] = p.childLeft(at, i)
	}
	return at
}

func (p *placer) childLeft(at placement, i int) int64 {
	parent := p.nodes[i].Parent
	if at.right[i] {
		return at.left[parent] + int64(p.nodes[parent].Width) + int64(p.gaps.Level)
	}
	return at.left[parent] - int64(p.gaps.Level) - int64(p.nodes[i].Width)
}

func rect(x, y, w, h int64) (geom.Rect, bool) {
	for _, v := range []int64{x, y, x + w, y + h} {
		if v < -geom.CoordLimit || v > geom.CoordLimit {
			return geom.Rect{}, false
		}
	}
	return geom.Rect{X: int32(x), Y: int32(y), W: int32(w), H: int32(h)}, true
}

func (p *placer) routeRight(parent, child geom.Rect, ends [2]int64) []geom.Point {
	from := int64(parent.X) + int64(parent.W)
	return elbow(from, int64(child.X), from+geom.FloorDiv(int64(p.gaps.Level), 2), ends)
}

func (p *placer) routeLeft(parent, child geom.Rect, ends [2]int64) []geom.Point {
	from := int64(parent.X)
	return elbow(from, int64(child.X)+int64(child.W), from-geom.FloorDiv(int64(p.gaps.Level), 2), ends)
}

func elbow(from, to, trunk int64, ends [2]int64) []geom.Point {
	start := geom.Point{X: int32(from), Y: int32(ends[0])}
	end := geom.Point{X: int32(to), Y: int32(ends[1])}
	if ends[0] == ends[1] {
		return []geom.Point{start, end}
	}
	return []geom.Point{start, {X: int32(trunk), Y: start.Y}, {X: int32(trunk), Y: end.Y}, end}
}

type bounds struct {
	minX, minY, maxX, maxY int64
}

func (b *bounds) include(x, y int64) {
	b.minX, b.minY = min(b.minX, x), min(b.minY, y)
	b.maxX, b.maxY = max(b.maxX, x), max(b.maxY, y)
}

func (l *Layout) bounds() bounds {
	first := l.Boxes[0]
	b := bounds{minX: int64(first.X), minY: int64(first.Y), maxX: int64(first.X), maxY: int64(first.Y)}
	for _, box := range l.Boxes {
		b.include(int64(box.X), int64(box.Y))
		b.include(int64(box.X)+int64(box.W), int64(box.Y)+int64(box.H))
	}
	for _, route := range l.Routes {
		for _, point := range route {
			b.include(int64(point.X), int64(point.Y))
		}
	}
	return b
}

func Normalize(l *Layout, margin int32) (geom.Size, error) {
	if len(l.Boxes) == 0 {
		return geom.Size{W: 2 * margin, H: 2 * margin}, nil
	}
	b := l.bounds()
	dx, dy := int64(margin)-b.minX, int64(margin)-b.minY
	w, h := b.maxX-b.minX+2*int64(margin), b.maxY-b.minY+2*int64(margin)
	if w > geom.CoordLimit || h > geom.CoordLimit {
		return geom.Size{}, geom.ErrOverflow
	}
	for i := range l.Boxes {
		l.Boxes[i].X, l.Boxes[i].Y = int32(int64(l.Boxes[i].X)+dx), int32(int64(l.Boxes[i].Y)+dy)
	}
	for _, route := range l.Routes {
		for i := range route {
			route[i].X, route[i].Y = int32(int64(route[i].X)+dx), int32(int64(route[i].Y)+dy)
		}
	}
	return geom.Size{W: int32(w), H: int32(h)}, nil
}
