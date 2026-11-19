package geom

import "math"

func rectValid(r Rect) bool {
	return int64(r.W) >= 0 && int64(r.H) >= 0 &&
		int64(r.X)+int64(r.W) <= int64(I32Max) &&
		int64(r.Y)+int64(r.H) <= int64(I32Max)
}

func boundsOk(x, y, w, h int64) bool {
	return w >= 0 && h >= 0 && w <= int64(I32Max) && h <= int64(I32Max) &&
		x >= int64(I32Min) && y >= int64(I32Min) &&
		x+w <= int64(I32Max) && y+h <= int64(I32Max)
}

func Translate(r Rect, dx, dy int32) (Rect, error) {
	if !rectValid(r) {
		return Rect{}, ErrDomain
	}
	nx, ny := int64(r.X)+int64(dx), int64(r.Y)+int64(dy)
	if !boundsOk(nx, ny, int64(r.W), int64(r.H)) {
		return Rect{}, ErrOverflow
	}
	return Rect{X: int32(nx), Y: int32(ny), W: r.W, H: r.H}, nil
}

func Inflate(r Rect, d int32) (Rect, error) {
	if !rectValid(r) {
		return Rect{}, ErrDomain
	}
	nx, ny := int64(r.X)-int64(d), int64(r.Y)-int64(d)
	nw, nh := int64(r.W)+2*int64(d), int64(r.H)+2*int64(d)
	if nw < 0 || nh < 0 {
		return Rect{}, ErrDomain
	}
	if !boundsOk(nx, ny, nw, nh) {
		return Rect{}, ErrOverflow
	}
	return Rect{X: int32(nx), Y: int32(ny), W: int32(nw), H: int32(nh)}, nil
}

func Union(a, b Rect) (Rect, error) {
	if !rectValid(a) || !rectValid(b) {
		return Rect{}, ErrDomain
	}
	mx := min(int64(a.X), int64(b.X))
	my := min(int64(a.Y), int64(b.Y))
	Mx := max(int64(a.X)+int64(a.W), int64(b.X)+int64(b.W))
	My := max(int64(a.Y)+int64(a.H), int64(b.Y)+int64(b.H))
	if !boundsOk(mx, my, Mx-mx, My-my) {
		return Rect{}, ErrOverflow
	}
	return Rect{X: int32(mx), Y: int32(my), W: int32(Mx - mx), H: int32(My - my)}, nil
}

func Intersects(a, b Rect) (bool, error) {
	if !rectValid(a) || !rectValid(b) {
		return false, ErrDomain
	}
	w := min(int64(a.X)+int64(a.W), int64(b.X)+int64(b.W)) - max(int64(a.X), int64(b.X))
	h := min(int64(a.Y)+int64(a.H), int64(b.Y)+int64(b.H)) - max(int64(a.Y), int64(b.Y))
	return w > 0 && h > 0, nil
}

func Contains(outer, inner Rect) (bool, error) {
	if !rectValid(outer) || !rectValid(inner) {
		return false, ErrDomain
	}
	ok := int64(inner.X) >= int64(outer.X) &&
		int64(inner.X)+int64(inner.W) <= int64(outer.X)+int64(outer.W) &&
		int64(inner.Y) >= int64(outer.Y) &&
		int64(inner.Y)+int64(inner.H) <= int64(outer.Y)+int64(outer.H)
	return ok, nil
}

func PlaceAfter(axis Axis, a Rect, gap int32, s Size) (Rect, error) {
	if !rectValid(a) || gap < 0 || s.W < 0 || s.H < 0 {
		return Rect{}, ErrDomain
	}
	var nx, ny int64
	if axis == AxisX {
		nx, ny = int64(a.X)+int64(a.W)+int64(gap), int64(a.Y)
	} else {
		nx, ny = int64(a.X), int64(a.Y)+int64(a.H)+int64(gap)
	}
	if !boundsOk(nx, ny, int64(s.W), int64(s.H)) {
		return Rect{}, ErrOverflow
	}
	return Rect{X: int32(nx), Y: int32(ny), W: s.W, H: s.H}, nil
}

func Compact(axis Axis, gap int32, items []Rect) ([]Rect, error) {
	if gap < 0 {
		return nil, ErrDomain
	}
	for _, it := range items {
		if !rectValid(it) {
			return nil, ErrDomain
		}
	}
	out := make([]Rect, len(items))
	cursor := compactCursor{sweep: sweepFor(axis), prevEnd: minInt64}
	for i, it := range items {
		pos, err := cursor.place(it, int64(gap))
		if err != nil {
			return nil, err
		}
		out[i] = cursor.sweep.place(it, pos)
	}
	return out, nil
}

const minInt64 = math.MinInt64

type compactCursor struct {
	sweep   axisSweep
	prevEnd int64
}

func (c *compactCursor) place(r Rect, gap int64) (int64, error) {
	pos := max(c.sweep.start(r), c.prevEnd)
	if !boundsOk(pos, c.sweep.crossStart(r), c.sweep.length(r), c.sweep.crossLength(r)) {
		return 0, ErrOverflow
	}
	c.prevEnd = pos + c.sweep.length(r) + gap
	return pos, nil
}

type axisSweep struct {
	vertical bool
}

func sweepFor(axis Axis) axisSweep {
	return axisSweep{vertical: axis == AxisY}
}

func (s axisSweep) start(r Rect) int64 {
	if s.vertical {
		return int64(r.Y)
	}
	return int64(r.X)
}

func (s axisSweep) length(r Rect) int64 {
	if s.vertical {
		return int64(r.H)
	}
	return int64(r.W)
}

func (s axisSweep) crossStart(r Rect) int64 {
	if s.vertical {
		return int64(r.X)
	}
	return int64(r.Y)
}

func (s axisSweep) crossLength(r Rect) int64 {
	if s.vertical {
		return int64(r.W)
	}
	return int64(r.H)
}

func (s axisSweep) place(r Rect, pos int64) Rect {
	if s.vertical {
		r.Y = int32(pos)
	} else {
		r.X = int32(pos)
	}
	return r
}
