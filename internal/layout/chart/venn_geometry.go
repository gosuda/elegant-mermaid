package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

const (
	vennHalfTurn  = 32768
	vennQ15       = 32768
	vennLensTurn  = 131072
	vennLensSine  = 20861
	vennThreeSets = 3
)

type vennSteps struct {
	acos, bisect int
	sqrt3Half    int64
}

type vennCircle struct{ x, y, r int64 }

func vennLargest(sizes []int64) int64 {
	largest := int64(1)
	for _, s := range sizes {
		largest = max(largest, s)
	}
	return largest
}

func vennRadii(sizes []int64, largest, radius int64) ([]int64, error) {
	out := make([]int64, len(sizes))
	for i, s := range sizes {
		q := mulUnsigned(uint64(radius*radius), uint64(max(s, 0))).divide(uint64(largest))
		root, err := geom.Isqrt(int64(q.lo))
		if err != nil {
			return nil, err
		}
		out[i] = root
	}
	return out, nil
}

func vennArccos(x int64, steps int) int64 {
	lo, hi := int64(0), int64(vennHalfTurn)
	for range steps {
		mid := geom.FloorDiv(lo+hi+1, 2)
		if int64(geom.CosQ15(int32(mid))) >= x {
			lo = mid
		} else {
			hi = mid - 1
		}
	}
	return lo
}

func vennHalfChord(d, own, other int64, steps int) int64 {
	x := geom.FloorDiv((d*d+own*own-other*other)*vennQ15, 2*d*own)
	return vennArccos(Clamp(x, -vennQ15, vennQ15), steps)
}

func vennLensArea(d, r1, r2 int64, steps int) wide {
	var area wide
	for _, pair := range [2][2]int64{{r1, r2}, {r2, r1}} {
		u := vennHalfChord(d, pair[0], pair[1], steps)
		turn := vennLensTurn*u - vennLensSine*int64(geom.SinQ15(int32(2*u)))
		area = area.add(mulSigned(uint64(pair[0]*pair[0]), turn))
	}
	return area
}

func vennDistance(r1, r2 int64, target wide, steps vennSteps) int64 {
	lo, hi := r1-r2, r1+r2
	if lo < 0 {
		lo = -lo
	}
	smaller := min(r1, r2)
	contained := wideOf(uint64(smaller * smaller))
	switch {
	case !contained.greater(target):
		return lo
	case target == wideOf(0):
		return hi
	}
	want := target.shiftLeft32()
	for range steps.bisect {
		mid := geom.FloorDiv(lo+hi, 2)
		if vennOverlapGreater(mid, r1, r2, contained, want, steps.acos) {
			lo = mid
		} else {
			hi = mid
		}
	}
	return geom.FloorDiv(lo+hi, 2)
}

func vennOverlapGreater(d, r1, r2 int64, contained, want wide, acos int) bool {
	if d == 0 {
		return contained.shiftLeft32().greater(want)
	}
	return vennLensArea(d, r1, r2, acos).greater(want)
}

func vennTarget(overlap, largest, radius int64) wide {
	return mulUnsigned(uint64(radius*radius), uint64(max(overlap, 0))).divide(uint64(max(largest, 1)))
}

func vennCentres(radii []int64, radius, distance int64, steps vennSteps) []vennCircle {
	out := make([]vennCircle, len(radii))
	for i, r := range radii {
		out[i].r = r
	}
	switch len(radii) {
	case 1:
		out[0].x, out[0].y = 2*radius, 2*radius
	case 2:
		out[0].x, out[0].y = 2*radius-geom.FloorDiv(distance, 2), 2*radius
		out[1].x, out[1].y = out[0].x+distance, 2*radius
	case vennThreeSets:
		dx := geom.FloorDiv(radius*steps.sqrt3Half, vennQ15)
		low := 2*radius + geom.FloorDiv(radius, 2)
		out[0].x, out[0].y = 2*radius, radius
		out[1].x, out[1].y = 2*radius+dx, low
		out[2].x, out[2].y = 2*radius-dx, low
	}
	return out
}
