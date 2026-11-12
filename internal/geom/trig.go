package geom

import "github.com/gosuda/elegant-mermaid/internal/gen"

func SinQ15(a int32) int32 {
	return sinAt(FloorMod(int64(a), 65536))
}

func CosQ15(a int32) int32 {
	return sinAt(FloorMod(int64(a)+16384, 65536))
}

func sinAt(r int64) int32 {
	q := FloorDiv(r, 16384)
	u := r - 16384*q
	switch q {
	case 1:
		return lookup(16384 - u)
	case 2:
		return -lookup(u)
	case 3:
		return -lookup(16384 - u)
	default:
		return lookup(u)
	}
}

func lookup(k int64) int32 {
	i := int(FloorDiv(k, 16))
	f := k - 16*int64(i)
	if f == 0 {
		return gen.SineTable[i]
	}
	delta := int64(gen.SineTable[i+1]) - int64(gen.SineTable[i])
	return gen.SineTable[i] + int32(FloorDiv(delta*f+8, 16))
}
