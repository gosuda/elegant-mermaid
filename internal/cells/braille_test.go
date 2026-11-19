package cells

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func naiveInside(p []geom.Point, x, y int64) bool {
	count := 0
	for i, a := range p {
		b := p[(i+1)%len(p)]
		if a.Y > b.Y {
			a, b = b, a
		}
		if y < int64(a.Y) || y >= int64(b.Y) {
			continue
		}
		dy := int64(b.Y) - int64(a.Y)
		left := (x - int64(a.X)) * dy
		right := (int64(b.X) - int64(a.X)) * (y - int64(a.Y))
		if left < right {
			count++
		}
	}
	return count%2 == 1
}

func TestFill(t *testing.T) {
	for _, p := range [][]geom.Point{{{}, {X: 1024}, {X: 1024, Y: 1024}, {Y: 1024}}, {{}, {X: 1024}, {Y: 1024}}} {
		c := canvas(t, 3, 2)
		if err := c.Fill(p, TokenLine); err != nil {
			t.Fatal(err)
		}
		for y := range 8 {
			for x := range 6 {
				v, _ := c.Cell(x/2, y/4)
				got := v.Dots&DotBit(x, y) != 0
				if got != naiveInside(p, int64(x*256+128), int64(y*256+128)) {
					t.Fatal(x, y)
				}
			}
		}
	}
}

func neighbouringDots(c *Canvas, p geom.Point) []geom.Point {
	var out []geom.Point
	for dy := int32(-1); dy <= 1; dy++ {
		for dx := int32(-1); dx <= 1; dx++ {
			q := geom.Point{X: p.X + dx, Y: p.Y + dy}
			if hasDot(c, q) {
				out = append(out, q)
			}
		}
	}
	return out
}

func hasDot(c *Canvas, p geom.Point) bool {
	if p.X < 0 || p.Y < 0 {
		return false
	}
	v, ok := c.Cell(int(p.X)/2, int(p.Y)/4)
	return ok && v.Dots&DotBit(int(p.X), int(p.Y)) != 0
}

func reachableDots(c *Canvas, a geom.Point) map[geom.Point]bool {
	seen := map[geom.Point]bool{a: true}
	queue := []geom.Point{a}
	for len(queue) > 0 {
		p := queue[0]
		queue = queue[1:]
		for _, q := range neighbouringDots(c, p) {
			if !seen[q] {
				seen[q] = true
				queue = append(queue, q)
			}
		}
	}
	return seen
}

func TestStrokeConnected(t *testing.T) {
	s := uint32(1)
	for range 2000 {
		s ^= s << 13
		s ^= s >> 17
		s ^= s << 5
		a := geom.Point{X: int32(s % 16), Y: int32(s >> 4 % 16)}
		b := geom.Point{X: int32(s >> 8 % 16), Y: int32(s >> 12 % 16)}
		c := canvas(t, 8, 4)
		if err := c.StrokeDots(a, b, TokenLine); err != nil {
			t.Fatal(err)
		}
		seen := reachableDots(c, a)
		if !seen[b] || len(seen) != len(dots(c)) {
			t.Fatal(a, b)
		}
	}
}
