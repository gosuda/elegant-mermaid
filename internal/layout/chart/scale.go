package chart

import (
	"errors"
	"math/bits"
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var ErrOverflow = geom.ErrOverflow

var errDomain = errors.New("chart layout: invalid geometry")

const (
	tickCount = 10
	tickCap   = 64
	scanCap   = 40
	scale     = 1000
)

type Linear struct {
	D0, D1 int64
	R0, R1 int64
}

func (l Linear) Map(v int64) int64 {
	if l.D1 == l.D0 {
		return geom.FloorDiv(l.R0+l.R1, 2)
	}
	return l.R0 + geom.FloorDiv((v-l.D0)*(l.R1-l.R0), l.D1-l.D0)
}

func BandPosition(index, count int, r0, r1 int64) int64 {
	span := r1 - r0
	if count < 2 {
		return r0 + geom.FloorDiv(span, 2)
	}
	return r0 + geom.FloorDiv(int64(index)*span, int64(count-1))
}

func Clamp(v, a, b int64) int64 {
	return max(min(v, max(a, b)), min(a, b))
}

func powerOfTen(e int) uint64 {
	p := uint64(1)
	for range e {
		p *= 10
	}
	return p
}

func atLeast(d2, s2, k uint64) bool {
	hi, lo := bits.Mul64(s2, k)
	return hi == 0 && d2 >= lo
}

func tickStep(d uint64) int64 {
	if d < tickCount {
		return 1
	}
	p := uint64(1)
	for e := range scanCap / 2 {
		if powerOfTen(e)*tickCount > d {
			break
		}
		p = powerOfTen(e)
	}
	s2 := tickCount * tickCount * p * p
	d2 := d * d
	switch {
	case atLeast(d2, s2, 50):
		return int64(10 * p)
	case atLeast(d2, s2, 10):
		return int64(5 * p)
	case atLeast(d2, s2, 2):
		return int64(2 * p)
	}
	return int64(p)
}

func Ticks(lo, hi int64) (ticks []int64, capped bool, err error) {
	span := hi - lo
	if span < 0 {
		span = -span
	}
	if span > int64(geom.I32Max) {
		return nil, false, ErrOverflow
	}
	if span == 0 {
		return []int64{lo}, false, nil
	}
	step := tickStep(uint64(span))
	first, last := min(lo, hi), max(lo, hi)
	for v := -geom.FloorDiv(-first, step) * step; v <= last; v += step {
		if len(ticks) == tickCap {
			capped = true
			break
		}
		ticks = append(ticks, v)
	}
	if lo > hi {
		slices.Reverse(ticks)
	}
	return ticks, capped, nil
}

func FormatNumber(thousandths int64) string {
	sign := ""
	if thousandths < 0 {
		sign, thousandths = "-", -thousandths
	}
	text := sign + strconv.FormatInt(thousandths/scale, 10)
	fraction := thousandths % scale
	if fraction == 0 {
		return text
	}
	digits := strconv.FormatInt(scale+fraction, 10)[1:]
	for digits[len(digits)-1] == '0' {
		digits = digits[:len(digits)-1]
	}
	return text + "." + digits
}
