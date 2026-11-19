package cells

import (
	"math"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func checkedPoint(x, y int64) (geom.Point, error) {
	if x < math.MinInt32 || x > math.MaxInt32 || y < math.MinInt32 || y > math.MaxInt32 {
		return geom.Point{}, geom.ErrOverflow
	}
	return geom.Point{X: int32(x), Y: int32(y)}, nil
}

func multiply(a, b int64) (int64, error) {
	if productOverflows(a, b) {
		return 0, geom.ErrOverflow
	}
	return a * b, nil
}

func productOverflows(a, b int64) bool {
	switch {
	case a > 0 && b > 0:
		return a > math.MaxInt64/b
	case a > 0 && b < 0:
		return b < math.MinInt64/a
	case a < 0 && b > 0:
		return a < math.MinInt64/b
	case a < 0 && b < 0:
		return a < math.MaxInt64/b
	default:
		return false
	}
}

func add(a, b int64) (int64, error) {
	if b > 0 && a > math.MaxInt64-b || b < 0 && a < math.MinInt64-b {
		return 0, geom.ErrOverflow
	}
	return a + b, nil
}

func NewBraille(w, h int32) (*Canvas, error) {
	if w < 0 || h < 0 {
		return nil, ErrNegativeSize
	}
	return New(int((int64(w)+511)/512), int((int64(h)+1023)/1024))
}

func DotBit(x, y int) uint8 {
	bits := [2][4]uint8{{1, 2, 4, 64}, {8, 16, 32, 128}}
	return bits[x&1][y&3]
}

func (c *Canvas) PutDot(x, y int, ink Token) {
	if x < 0 || y < 0 {
		return
	}
	c.Put(x/2, y/4, func(v *Cell) { v.Dots |= DotBit(x, y); v.Ink = max(v.Ink, ink) })
}
func CellDot(p geom.Point) (geom.Point, error) { return checkedPoint(2*int64(p.X), 4*int64(p.Y)+2) }
func abs(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func (c *Canvas) StrokeDots(a, b geom.Point, ink Token) error {
	x, y := int64(a.X), int64(a.Y)
	tx, ty := int64(b.X), int64(b.Y)
	dx, dy := abs(tx-x), -abs(ty-y)
	sx, sy := int64(-1), int64(-1)
	if x < tx {
		sx = 1
	}
	if y < ty {
		sy = 1
	}
	e := dx + dy
	for fuel := dx - dy + 1; fuel > 0; fuel-- {
		c.PutDot(int(x), int(y), ink)
		if x == tx && y == ty {
			return nil
		}
		e2 := 2 * e
		if e2 >= dy {
			e += dy
			x += sx
		}
		if e2 <= dx {
			e += dx
			y += sy
		}
	}
	return nil
}

func (c *Canvas) Stroke(points []geom.Point, ink Token) error {
	for i := 1; i < len(points); i++ {
		a, b := points[i-1], points[i]
		a.X = int32(geom.FloorDiv(int64(a.X), 256))
		a.Y = int32(geom.FloorDiv(int64(a.Y), 256))
		b.X = int32(geom.FloorDiv(int64(b.X), 256))
		b.Y = int32(geom.FloorDiv(int64(b.Y), 256))
		if err := c.StrokeDots(a, b, ink); err != nil {
			return err
		}
	}
	return nil
}

func edgeCross(a, b geom.Point, px, py int64) (bool, error) {
	y1, y2 := int64(a.Y), int64(b.Y)
	if (y1 > py || py >= y2) && (y2 > py || py >= y1) {
		return false, nil
	}
	u, err := multiply(int64(b.X)-int64(a.X), py-y1)
	if err != nil {
		return false, err
	}
	v, err := multiply(int64(a.X)-px, y2-y1)
	if err != nil {
		return false, err
	}
	n, err := add(u, v)
	if err != nil {
		return false, err
	}
	n, err = multiply(n, y2-y1)
	return n > 0, err
}

func polygonInside(points []geom.Point, x, y int64) (bool, error) {
	inside := false
	for i, a := range points {
		b := points[(i+1)%len(points)]
		cross, err := edgeCross(a, b, x, y)
		if err != nil {
			return false, err
		}
		if cross {
			inside = !inside
		}
	}
	return inside, nil
}

func ringsInside(rings [][]geom.Point, x, y int64) (bool, error) {
	inside := false
	for _, ring := range rings {
		in, err := polygonInside(ring, x, y)
		if err != nil {
			return false, err
		}
		inside = inside != in
	}
	return inside, nil
}

func (c *Canvas) dotWindow(rings [][]geom.Point) (x0, x1, y0, y1 int, ok bool) {
	first := true
	var lo, hi geom.Point
	for _, ring := range rings {
		for _, p := range ring {
			if first {
				lo, hi, first = p, p, false
				continue
			}
			lo.X, lo.Y = min(lo.X, p.X), min(lo.Y, p.Y)
			hi.X, hi.Y = max(hi.X, p.X), max(hi.Y, p.Y)
		}
	}
	if first {
		return 0, 0, 0, 0, false
	}
	x0 = int(max(0, geom.FloorDiv(int64(lo.X), 256)))
	y0 = int(max(0, geom.FloorDiv(int64(lo.Y), 256)))
	x1 = int(min(int64(c.W*2-1), geom.FloorDiv(int64(hi.X), 256)))
	y1 = int(min(int64(c.H*4-1), geom.FloorDiv(int64(hi.Y), 256)))
	return x0, x1, y0, y1, x0 <= x1 && y0 <= y1
}

func (c *Canvas) FillRings(rings [][]geom.Point, ink Token) error {
	x0, x1, y0, y1, ok := c.dotWindow(rings)
	if !ok {
		return nil
	}
	for y := y0; y <= y1; y++ {
		for x := x0; x <= x1; x++ {
			inside, err := ringsInside(rings, 256*int64(x)+128, 256*int64(y)+128)
			if err != nil {
				return err
			}
			if inside {
				c.PutDot(x, y, ink)
			}
		}
	}
	return nil
}

func (c *Canvas) Fill(points []geom.Point, ink Token) error {
	return c.FillRings([][]geom.Point{points}, ink)
}

func Arc(center geom.Point, radius, start, sweep int32) ([]geom.Point, error) {
	n := max(int64(4), (abs(int64(sweep))+1023)/1024)
	out := make([]geom.Point, n+1)
	for k := range n + 1 {
		a := int64(start) + geom.FloorDiv(int64(sweep)*k, n)
		a = geom.FloorMod(a, 65536)
		x := int64(center.X) + geom.FloorDiv(2*int64(radius)*int64(geom.CosQ15(int32(a)))+32768, 65536)
		y := int64(center.Y) + geom.FloorDiv(2*int64(radius)*int64(geom.SinQ15(int32(a)))+32768, 65536)
		p, err := checkedPoint(x, y)
		if err != nil {
			return nil, err
		}
		out[k] = p
	}
	return out, nil
}

func Ellipse(center geom.Point, rx, ry int32) ([]geom.Point, error) {
	out := make([]geom.Point, 64)
	for j := range 64 {
		a := int32(j * 1024)
		x := int64(center.X) + geom.FloorDiv(int64(rx)*int64(geom.CosQ15(a)), 32768)
		y := int64(center.Y) - geom.FloorDiv(int64(ry)*int64(geom.SinQ15(a)), 32768)
		p, err := checkedPoint(x, y)
		if err != nil {
			return nil, err
		}
		out[j] = p
	}
	return out, nil
}

func cubicAxis(v [4]int32, k int64) int64 {
	t := 16 - k
	return geom.FloorDiv(t*t*t*int64(v[0])+3*k*t*t*int64(v[1])+3*k*k*t*int64(v[2])+k*k*k*int64(v[3])+2048, 4096)
}

func Cubic(p [4]geom.Point) ([]geom.Point, error) {
	out := make([]geom.Point, 17)
	for k := range int64(17) {
		x := cubicAxis([4]int32{p[0].X, p[1].X, p[2].X, p[3].X}, k)
		y := cubicAxis([4]int32{p[0].Y, p[1].Y, p[2].Y, p[3].Y}, k)
		v, err := checkedPoint(x, y)
		if err != nil {
			return nil, err
		}
		out[k] = v
	}
	return out, nil
}
