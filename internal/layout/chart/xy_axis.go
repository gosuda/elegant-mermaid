package chart

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
)

type position uint8

const (
	posBottom position = iota
	posLeft
	posTop
)

type bandSpace struct {
	w, h      int64
	line      int64
	tick      int64
	title     int64
	showLabel bool
}
type axis struct {
	position   position
	band       bool
	categories []string
	distinct   []int
	n          int
	lo, hi     int64
	ticks      []int64
	labels     []string
	title      string
	showLabels bool
	fontSize   int32
	outer      int64
	r0, r1     int64
	space      bandSpace
	area       rect
	labelW     int64
	labelH     int64
}

func (a *axis) count() int { return len(a.labels) }

func (a *axis) innerRange() (int64, int64) { return a.r0 + a.outer, a.r1 - a.outer }

func (a *axis) tickDistance() int64 {
	if a.count() == 0 {
		return 0
	}
	lo, hi := a.innerRange()
	return geom.FloorDiv(max(hi-lo, lo-hi), int64(a.count()))
}

func (a *axis) raiseOuterForBars(ratio int64) {
	dist := a.tickDistance()
	if ratio*dist > 2000*a.outer {
		a.outer = geom.FloorDiv(ratio*dist, 2000)
	}
}

func (a *axis) bandIndex(slot int) (int, bool) {
	if slot < 0 || slot >= len(a.distinct) {
		return 0, false
	}
	return a.distinct[slot], true
}

func (a *axis) linear() Linear {
	lo, hi := a.innerRange()
	d0, d1 := a.lo, a.hi
	if a.position == posLeft {
		d0, d1 = d1, d0
	}
	return Linear{D0: d0, D1: d1, R0: lo, R1: hi}
}

func (a *axis) clampPosition(v, edge int64) int64 {
	return Clamp(v, a.r0, a.r1-edge)
}

func (a *axis) bandPosition(slot int, edge int64) int64 {
	lo, hi := a.innerRange()
	index, ok := a.bandIndex(slot)
	if !ok {
		return a.clampPosition(lo, edge)
	}
	return a.clampPosition(BandPosition(index, a.n, lo, hi), edge)
}

func (a *axis) valuePosition(v int64, edge int64) int64 {
	return a.clampPosition(a.linear().Map(Clamp(v, a.lo, a.hi)), edge)
}

func (a *axis) pointPosition(p chartmodel.Point, edge int64) int64 {
	if a.band {
		return a.bandPosition(p.Slot, edge)
	}
	if !p.HasX {
		return a.clampPosition(a.r0+a.outer, edge)
	}
	return a.valuePosition(int64(p.X), edge)
}

func (a *axis) tickPosition(k int, edge int64) int64 {
	if a.band {
		return a.bandPosition(k, edge)
	}
	return a.valuePosition(a.ticks[k], edge)
}

func distinctIndex(categories []string) ([]int, int) {
	first := make(map[string]int, len(categories))
	out := make([]int, len(categories))
	for i, name := range categories {
		at, seen := first[name]
		if !seen {
			at = len(first)
			first[name] = at
		}
		out[i] = at
	}
	return out, len(first)
}

func checkMagnitude(values ...int64) error {
	for _, v := range values {
		if v > int64(geom.I32Max) || v < -int64(geom.I32Max) {
			return ErrOverflow
		}
	}
	return nil
}

func linearAxis(lo, hi int64) (a axis, capped bool, err error) {
	if err = checkMagnitude(lo, hi); err != nil {
		return axis{}, false, err
	}
	a.lo, a.hi = lo, hi
	a.ticks, capped, err = Ticks(lo, hi)
	if err != nil {
		return axis{}, false, err
	}
	for _, t := range a.ticks {
		a.labels = append(a.labels, FormatNumber(t))
	}
	return a, capped, nil
}

func newAxes(xy *chartmodel.XY) (x, y axis, capped bool, err error) {
	y, capped, err = linearAxis(int64(xy.YAxis.Min), int64(xy.YAxis.Max))
	if err != nil {
		return axis{}, axis{}, false, err
	}
	if xy.XAxis.Band {
		x.band, x.categories, x.labels = true, xy.XAxis.Categories, xy.XAxis.Categories
		x.distinct, x.n = distinctIndex(x.categories)
		return x, y, capped, nil
	}
	x, xCapped, err := linearAxis(int64(xy.XAxis.Min), int64(xy.XAxis.Max))
	return x, y, capped || xCapped, err
}
