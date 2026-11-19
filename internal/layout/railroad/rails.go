package railroad

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const quarterTurn int32 = 16384

var railShape = scene.Shape{Style: "edge"}

func (l *layouter) rightStart(kid *shape, x int64) int64 {
	if l.p.isCell() && kid.node.Kind.leaf() {
		return x - 1
	}
	return x
}

func (l *layouter) rails(s *shape, x, y int64) []scene.Primitive {
	var polylines [][]point
	switch s.node.Kind {
	case KindChoice:
		polylines = l.choiceRails(s)
	case KindOptional:
		polylines = append(l.forwardRails(s), l.bypassRail(s))
	case KindZeroOrMore:
		polylines = append(l.forwardRails(s), l.loopRail(s), l.bypassRail(s))
	case KindOneOrMore:
		polylines = append(l.forwardRails(s), l.loopRail(s))
	}
	items := make([]scene.Primitive, len(polylines))
	for i, polyline := range polylines {
		items[i] = l.rail(translate(polyline, x, y))
	}
	return items
}

func translate(points []point, dx, dy int64) []point {
	out := make([]point, len(points))
	for i, p := range points {
		out[i] = point{p.x + dx, p.y + dy}
	}
	return out
}

func (l *layouter) choiceRails(s *shape) [][]point {
	r, cy := l.k.ArcRadius, s.centre()
	var out [][]point
	for i, kid := range s.kids {
		off := s.offsets[i]
		ecy := off.y + kid.up
		left := []point{{0, cy}}
		right := []point{{l.rightStart(kid, off.x+kid.w), ecy}}
		if ecy != cy {
			left = append(left, point{r, cy}, point{r, ecy})
			right = append(right, point{s.w - r, ecy}, point{s.w - r, cy})
		}
		out = append(out, append(left, point{off.x, ecy}), append(right, point{s.w, cy}))
	}
	return out
}

func (l *layouter) forwardRails(s *shape) [][]point {
	kid, cy, r := s.kids[0], s.centre(), l.k.ArcRadius
	return [][]point{
		{{0, cy}, {2 * r, cy}},
		{{l.rightStart(kid, 2*r+kid.w), cy}, {s.w, cy}},
	}
}

func (l *layouter) bypassRail(s *shape) []point {
	cy, r := s.centre(), l.k.ArcRadius
	return []point{{0, cy}, {r, cy}, {r, 0}, {s.w - r, 0}, {s.w - r, cy}, {s.w, cy}}
}

func (l *layouter) loopRail(s *shape) []point {
	kid, cy, r := s.kids[0], s.centre(), l.k.ArcRadius
	bottom := s.height()
	if l.p.isCell() {
		bottom--
	}
	end := 2*r + kid.w
	return []point{{l.rightStart(kid, end), cy}, {end + r, cy}, {end + r, bottom}, {r, bottom}, {r, cy}, {2 * r, cy}}
}

func (l *layouter) rail(points []point) scene.Primitive {
	points = compact(points)
	if l.p.isCell() {
		out := make([]geom.Point, len(points))
		for i, p := range points {
			out[i] = pointOf(p)
		}
		return &scene.Polyline{Shape: railShape, Points: out}
	}
	return &scene.Path{Shape: railShape, Commands: l.rounded(points)}
}

func compact(points []point) []point {
	out := points[:1:1]
	for _, p := range points[1:] {
		if p != out[len(out)-1] {
			out = append(out, p)
		}
	}
	return out
}

func sign(v int64) int64 {
	switch {
	case v > 0:
		return 1
	case v < 0:
		return -1
	}
	return 0
}

func unit(from, to point) point { return point{sign(to.x - from.x), sign(to.y - from.y)} }

func legLength(from, to point) int64 {
	return max(to.x-from.x, from.x-to.x) + max(to.y-from.y, from.y-to.y)
}

func quarterAngle(v point) int32 {
	switch {
	case v.x > 0:
		return 0
	case v.y > 0:
		return quarterTurn
	case v.x < 0:
		return 2 * quarterTurn
	}
	return 3 * quarterTurn
}

func (l *layouter) cornerRadius(points []point, k int) int64 {
	last := len(points) - 1
	in := legLength(points[k-1], points[k])
	out := legLength(points[k], points[k+1])
	if k-1 > 0 {
		in = geom.FloorDiv(in, 2)
	}
	if k+1 < last {
		out = geom.FloorDiv(out, 2)
	}
	return min(l.k.ArcRadius, in, out)
}

func (l *layouter) rounded(points []point) []scene.Command {
	commands := []scene.Command{&scene.MoveTo{P: pointOf(points[0])}}
	for k := 1; k < len(points)-1; k++ {
		in, out := unit(points[k-1], points[k]), unit(points[k], points[k+1])
		turn := in.x*out.y - in.y*out.x
		radius := l.cornerRadius(points, k)
		if turn == 0 || radius == 0 {
			commands = append(commands, &scene.LineTo{P: pointOf(points[k])})
			continue
		}
		start := point{points[k].x - radius*in.x, points[k].y - radius*in.y}
		centre := point{start.x + radius*out.x, start.y + radius*out.y}
		sweep := quarterTurn
		if turn < 0 {
			sweep = -quarterTurn
		}
		commands = append(commands,
			&scene.LineTo{P: pointOf(start)},
			&scene.ArcTo{CX: int32(centre.x), CY: int32(centre.y), R: int32(radius), A0: quarterAngle(point{-out.x, -out.y}), Sweep: sweep})
	}
	return append(commands, &scene.LineTo{P: pointOf(points[len(points)-1])})
}
