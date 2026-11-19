package chart

import "math/bits"

type wide struct{ hi, lo uint64 }

func wideOf(v uint64) wide { return wide{lo: v} }

func mulUnsigned(a, b uint64) wide {
	hi, lo := bits.Mul64(a, b)
	return wide{hi, lo}
}

func (a wide) add(b wide) wide {
	lo, carry := bits.Add64(a.lo, b.lo, 0)
	hi, _ := bits.Add64(a.hi, b.hi, carry)
	return wide{hi, lo}
}

func (a wide) negate() wide {
	lo, carry := bits.Add64(^a.lo, 1, 0)
	return wide{^a.hi + carry, lo}
}

func (a wide) shiftLeft32() wide {
	return wide{a.hi<<32 | a.lo>>32, a.lo << 32}
}

func (a wide) greater(b wide) bool {
	if int64(a.hi) != int64(b.hi) {
		return int64(a.hi) > int64(b.hi)
	}
	return a.lo > b.lo
}

func mulSigned(a uint64, b int64) wide {
	if b >= 0 {
		return mulUnsigned(a, uint64(b))
	}
	return mulUnsigned(a, uint64(-b)).negate()
}

func (a wide) divide(d uint64) wide {
	hi := a.hi / d
	quotient, _ := bits.Div64(a.hi%d, a.lo, d)
	return wide{hi, quotient}
}
