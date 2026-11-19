package geom

func axisAligned(s Segment) bool {
	return s.A.X == s.B.X || s.A.Y == s.B.Y
}

func SegmentsCross(s, t Segment) (bool, error) {
	if !axisAligned(s) || !axisAligned(t) {
		return false, ErrDomain
	}
	if s.A == s.B || t.A == t.B {
		return false, nil
	}
	return crossByOrientation(s, t), nil
}

func crossByOrientation(s, t Segment) bool {
	switch {
	case isHorizontal(s) && isHorizontal(t):
		return horizontalCross(s, t)
	case isHorizontal(t):
		return perpendicularCross(t, s)
	case isHorizontal(s):
		return perpendicularCross(s, t)
	default:
		return verticalCross(s, t)
	}
}

func isHorizontal(s Segment) bool {
	return s.A.Y == s.B.Y
}

func horizontalCross(s, t Segment) bool {
	if s.A.Y != t.A.Y {
		return false
	}
	slo, shi := segXSpan(s)
	tlo, thi := segXSpan(t)
	return intervalsOverlap(slo, shi, tlo, thi)
}

func verticalCross(s, t Segment) bool {
	if s.A.X != t.A.X {
		return false
	}
	slo, shi := segYSpan(s)
	tlo, thi := segYSpan(t)
	return intervalsOverlap(slo, shi, tlo, thi)
}

func perpendicularCross(horizontal, vertical Segment) bool {
	hlo, hhi := segXSpan(horizontal)
	vlo, vhi := segYSpan(vertical)
	return spanContains(hlo, hhi, int64(vertical.A.X)) && spanContains(vlo, vhi, int64(horizontal.A.Y))
}

func spanContains(lo, hi, v int64) bool {
	return lo < v && v < hi
}

func intervalsOverlap(lo1, hi1, lo2, hi2 int64) bool {
	return max(lo1, lo2) < min(hi1, hi2)
}

func segXSpan(s Segment) (int64, int64) {
	return min(int64(s.A.X), int64(s.B.X)), max(int64(s.A.X), int64(s.B.X))
}

func segYSpan(s Segment) (int64, int64) {
	return min(int64(s.A.Y), int64(s.B.Y)), max(int64(s.A.Y), int64(s.B.Y))
}

func IsOrthogonal(p []Point) bool {
	for i := 1; i < len(p); i++ {
		if p[i].X != p[i-1].X && p[i].Y != p[i-1].Y {
			return false
		}
	}
	return true
}

func PolylineHitsRect(p []Point, r Rect) (bool, error) {
	if err := validateHitsRect(p, r); err != nil {
		return false, err
	}
	if r.W == 0 || r.H == 0 {
		return false, nil
	}
	if len(p) < 2 {
		return len(p) == 1 && pointInOpen(p[0], r), nil
	}
	prev := p[0]
	for _, cur := range p[1:] {
		if segHitsRect(prev, cur, r) {
			return true, nil
		}
		prev = cur
	}
	return false, nil
}

func validateHitsRect(p []Point, r Rect) error {
	if !rectValid(r) || !edgesWithinLimit(r) {
		return ErrDomain
	}
	for _, q := range p {
		if !withinLimit(int64(q.X)) || !withinLimit(int64(q.Y)) {
			return ErrDomain
		}
	}
	return nil
}

func withinLimit(v int64) bool {
	return v >= -CoordLimit && v <= CoordLimit
}

func edgesWithinLimit(r Rect) bool {
	return withinLimit(int64(r.X)) && withinLimit(int64(r.X)+int64(r.W)) &&
		withinLimit(int64(r.Y)) && withinLimit(int64(r.Y)+int64(r.H))
}

func pointInOpen(p Point, r Rect) bool {
	return int64(p.X) > int64(r.X) && int64(p.X) < int64(r.X)+int64(r.W) &&
		int64(p.Y) > int64(r.Y) && int64(p.Y) < int64(r.Y)+int64(r.H)
}

func segHitsRect(a, b Point, r Rect) bool {
	x0, y0 := int64(r.X), int64(r.Y)
	x1, y1 := x0+int64(r.W), y0+int64(r.H)
	ax, ay, bx, by := int64(a.X), int64(a.Y), int64(b.X), int64(b.Y)
	if max(ax, bx) <= x0 || min(ax, bx) >= x1 || max(ay, by) <= y0 || min(ay, by) >= y1 {
		return false
	}
	if a == b {
		return true
	}
	nx, ny := ay-by, bx-ax
	c := nx*ax + ny*ay
	d0 := nx*x0 + ny*y0
	d1 := nx*x1 + ny*y0
	d2 := nx*x1 + ny*y1
	d3 := nx*x0 + ny*y1
	m := min(min(d0, d1), min(d2, d3))
	M := max(max(d0, d1), max(d2, d3))
	return c > m && c < M
}
