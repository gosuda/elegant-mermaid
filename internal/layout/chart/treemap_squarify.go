package chart

import (
	"math"
	"math/bits"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

const maxSquarifyTotal = 1 << 31

type u128 struct{ hi, lo uint64 }

func mulU128(a, b uint64) u128 {
	hi, lo := bits.Mul64(a, b)
	return u128{hi, lo}
}

func shiftU128(a uint64, n uint) u128 {
	switch {
	case n >= 64:
		return u128{hi: a << (n - 64)}
	case n == 0:
		return u128{lo: a}
	}
	return u128{hi: a >> (64 - n), lo: a << n}
}

func (x u128) cmp(y u128) int {
	switch {
	case x.hi < y.hi:
		return -1
	case x.hi > y.hi:
		return 1
	case x.lo < y.lo:
		return -1
	case x.lo > y.lo:
		return 1
	}
	return 0
}

func (x u128) scale(s uint64) (u128, error) {
	carryLo, lo := bits.Mul64(x.lo, s)
	overflow, hi := bits.Mul64(x.hi, s)
	hi, carry := bits.Add64(hi, carryLo, 0)
	if overflow != 0 || carry != 0 {
		return u128{}, ErrOverflow
	}
	return u128{hi, lo}, nil
}

func (x u128) sub(y u128) u128 {
	lo, borrow := bits.Sub64(x.lo, y.lo, 0)
	hi, _ := bits.Sub64(x.hi, y.hi, borrow)
	return u128{hi, lo}
}

func (x u128) bit(i int) uint64 {
	if i >= 64 {
		return (x.hi >> (i - 64)) & 1
	}
	return (x.lo >> i) & 1
}

func quotient(n, d u128) u128 {
	if d.hi == 0 && n.hi < d.lo {
		q, _ := bits.Div64(n.hi, n.lo, d.lo)
		return u128{lo: q}
	}
	var q, r u128
	for i := 127; i >= 0; i-- {
		carry := r.hi >> 63
		r = u128{hi: r.hi<<1 | r.lo>>63, lo: r.lo<<1 | n.bit(i)}
		if carry != 0 || r.cmp(d) >= 0 {
			r = r.sub(d)
			if i >= 64 {
				q.hi |= 1 << (i - 64)
			} else {
				q.lo |= 1 << i
			}
		}
	}
	return q
}

func maxU128(a, b u128) u128 {
	if a.cmp(b) >= 0 {
		return a
	}
	return b
}

type tile struct{ x0, y0, x1, y1 int64 }

func roundDiv(a, b int64) int64 { return geom.FloorDiv(2*a+b, 2*b) }

func rowAspect(largest, smallest, sum uint64, alpha u128) (u128, error) {
	beta, err := alpha.scale(sum * sum)
	if err != nil {
		return u128{}, err
	}
	if beta == (u128{}) {
		return u128{}, errDomain
	}
	return maxU128(quotient(shiftU128(largest, 80), beta), quotient(beta, u128{lo: smallest})), nil
}

type freeSpace struct{ dx, dy, remaining int64 }

func rowAlpha(free freeSpace, rho uint64) (u128, error) {
	denominator := mulU128(uint64(min(free.dx, free.dy))*uint64(free.remaining), rho)
	if denominator == (u128{}) {
		return u128{}, errDomain
	}
	return quotient(shiftU128(uint64(max(free.dx, free.dy)), 70), denominator), nil
}

func rowStart(values []int64, first int) (end int, sum int64) {
	end = first
	for {
		sum = values[end]
		end++
		if sum != 0 || end == len(values) {
			return end, sum
		}
	}
}

func growRow(values []int64, end int, sum int64, alpha u128) (int, int64, error) {
	smallest, largest, total := uint64(sum), uint64(sum), uint64(sum)
	aspect, err := rowAspect(largest, smallest, total, alpha)
	if err != nil {
		return 0, 0, err
	}
	for ; end < len(values) && values[end] != 0; end++ {
		v := uint64(values[end])
		next, err := rowAspect(max(largest, v), min(smallest, v), total+v, alpha)
		if err != nil {
			return 0, 0, err
		}
		if next.cmp(aspect) > 0 {
			break
		}
		aspect, total, smallest, largest = next, total+v, min(smallest, v), max(largest, v)
	}
	return end, int64(total), nil
}

func nextRow(values []int64, first int, free freeSpace, rho uint64) (end int, sum int64, err error) {
	end, sum = rowStart(values, first)
	if sum == 0 {
		return end, 0, nil
	}
	if min(free.dx, free.dy) == 0 {
		return len(values), free.remaining, nil
	}
	alpha, err := rowAlpha(free, rho)
	if err != nil {
		return 0, 0, err
	}
	return growRow(values, end, sum, alpha)
}

func squarify(values []int64, area tile, rho uint64, fuel int) (cells []tile, capped bool, err error) {
	remaining, err := squarifyTotal(values)
	if err != nil {
		return nil, false, err
	}
	if remaining > maxSquarifyTotal || rho == 0 || area.x1 < area.x0 || area.y1 < area.y0 {
		return nil, false, errDomain
	}
	cells = make([]tile, len(values))
	for first, rows := 0, 0; first < len(values); rows++ {
		end, sum := len(values), remaining
		if rows < fuel {
			free := freeSpace{dx: area.x1 - area.x0, dy: area.y1 - area.y0, remaining: remaining}
			if end, sum, err = nextRow(values, first, free, rho); err != nil {
				return nil, false, err
			}
		} else {
			capped = true
		}
		area = placeRow(cells[first:end], values[first:end], area, rowTotals{sum: sum, remaining: remaining})
		remaining -= sum
		first = end
	}
	return cells, capped, nil
}

func squarifyTotal(values []int64) (int64, error) {
	var total int64
	for _, v := range values {
		if v < 0 {
			return 0, errDomain
		}
		if total > math.MaxInt64-v {
			return 0, ErrOverflow
		}
		total += v
	}
	return total, nil
}

type rowTotals struct{ sum, remaining int64 }

func placeRow(cells []tile, values []int64, area tile, totals rowTotals) tile {
	sum, remaining := totals.sum, totals.remaining
	dx, dy := area.x1-area.x0, area.y1-area.y0
	dice := dx < dy
	along, across := dx, dy
	if !dice {
		along, across = dy, dx
	}
	thickness := across
	if sum > 0 && remaining > 0 {
		thickness = roundDiv(across*sum, remaining)
	}
	var cumulative, previous int64
	for k, v := range values {
		cumulative += v
		var boundary int64
		if sum > 0 {
			boundary = roundDiv(along*cumulative, sum)
		}
		if dice {
			cells[k] = tile{area.x0 + previous, area.y0, area.x0 + boundary, area.y0 + thickness}
		} else {
			cells[k] = tile{area.x0, area.y0 + previous, area.x0 + thickness, area.y0 + boundary}
		}
		previous = boundary
	}
	if dice {
		area.y0 += thickness
	} else {
		area.x0 += thickness
	}
	return area
}
