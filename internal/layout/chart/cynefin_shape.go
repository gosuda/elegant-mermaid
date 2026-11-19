package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	foldPoints     = 8
	foldDraws      = 15
	foldWhole      = int64(1) << 32
	cliffAmplitude = 3
)

type xorshift32 uint32

func (s *xorshift32) next() uint32 {
	v := uint32(*s)
	v ^= v << 13
	v ^= v >> 17
	v ^= v << 5
	*s = xorshift32(v)
	return v
}

type foldCurve struct {
	points [foldPoints]curvePoint
	offset [foldPoints - 1]int64
}

func newFold(seed uint32, cx, height, amplitude, waves int64) foldCurve {
	gen := xorshift32(seed)
	var draws [foldDraws]int64
	for i := range draws {
		draws[i] = int64(gen.next())
	}
	var f foldCurve
	for i := range f.points {
		f.points[i] = curvePoint{
			x: cx + geom.FloorDiv(draws[i]*2*amplitude, foldWhole) - amplitude,
			y: geom.FloorDiv(int64(i)*height, waves),
		}
	}
	for i := range f.offset {
		dir := int64(1)
		if i%2 == 1 {
			dir = -1
		}
		f.offset[i] = dir * geom.FloorDiv(3*amplitude*draws[foldPoints+i], foldWhole*2)
	}
	return f
}

func (f foldCurve) path() (*scene.Path, error) {
	start, err := pointOf(f.points[0].x, f.points[0].y)
	if err != nil {
		return nil, err
	}
	commands := []scene.Command{&scene.MoveTo{P: start}}
	for i, off := range f.offset {
		p0, p1 := f.points[i], f.points[i+1]
		mid := geom.FloorDiv(p0.y+p1.y, 2)
		c1, err := pointOf(p0.x+off, mid)
		if err != nil {
			return nil, err
		}
		c2, err := pointOf(p1.x-off, mid)
		if err != nil {
			return nil, err
		}
		end, err := pointOf(p1.x, p1.y)
		if err != nil {
			return nil, err
		}
		commands = append(commands, &scene.CubicTo{C1: c1, C2: c2, P: end})
	}
	return &scene.Path{Shape: scene.Shape{Style: "rule"}, Commands: commands}, nil
}

func (f foldCurve) linePath() (*scene.Path, error) {
	start, err := pointOf(f.points[0].x, f.points[0].y)
	if err != nil {
		return nil, err
	}
	commands := []scene.Command{&scene.MoveTo{P: start}}
	for _, p := range f.points[1:] {
		at, err := pointOf(p.x, p.y)
		if err != nil {
			return nil, err
		}
		commands = append(commands, &scene.LineTo{P: at})
	}
	return &scene.Path{Shape: scene.Shape{Style: "rule"}, Commands: commands}, nil
}

func cliffPath(width, height, cx, cy int64) (*scene.Path, error) {
	a := geom.FloorDiv(width*cliffAmplitude, 100)
	dh := height - cy
	at := func(dx, percent int64) curvePoint { return curvePoint{cx + dx, cy + geom.FloorDiv(dh*percent, 100)} }
	nodes := [...]curvePoint{
		{cx, cy},
		at(a, 20), at(-geom.FloorDiv(3*a, 2), 55), at(geom.FloorDiv(a, 2), 75),
		at(-a, 85), at(geom.FloorDiv(3*a, 10), 95), {cx, height},
	}
	var points [len(nodes)]geom.Point
	for i, n := range nodes {
		p, err := pointOf(n.x, n.y)
		if err != nil {
			return nil, err
		}
		points[i] = p
	}
	return &scene.Path{Shape: scene.Shape{Style: "rule"}, Commands: []scene.Command{
		&scene.MoveTo{P: points[0]},
		&scene.CubicTo{C1: points[1], C2: points[2], P: points[3]},
		&scene.CubicTo{C1: points[4], C2: points[5], P: points[6]},
	}}, nil
}
