package geom

import "errors"

type Point struct {
	X, Y int32
}

type Size struct {
	W, H int32
}

type Segment struct {
	A, B Point
}

type Rect struct {
	X, Y, W, H int32
}

type Axis uint8

const (
	AxisX Axis = iota
	AxisY
)

const (
	I32Min     int32 = -2147483648
	I32Max     int32 = 2147483647
	CoordLimit int64 = 1 << 29
	isqrtTop   int64 = 4611686018427387904
)

var (
	ErrOverflow = errors.New("arithmetic overflow")
	ErrDomain   = errors.New("domain error")
)

func FloorDiv(a, b int64) int64 {
	q := a / b
	if a%b != 0 && (a < 0) != (b < 0) {
		q--
	}
	return q
}

func FloorMod(a, b int64) int64 {
	return a - FloorDiv(a, b)*b
}

func CountInversions(xs []int32) (int32, error) {
	a := make([]int32, len(xs))
	copy(a, xs)
	n := mergeCount(a, make([]int32, len(xs)))
	if n > int64(I32Max) {
		return 0, ErrOverflow
	}
	return int32(n), nil
}

func mergeCount(a, tmp []int32) int64 {
	n := len(a)
	if n < 2 {
		return 0
	}
	mid := n / 2
	count := mergeCount(a[:mid], tmp) + mergeCount(a[mid:], tmp)
	i, j, k := 0, mid, 0
	for i < mid && j < n {
		if a[i] <= a[j] {
			tmp[k] = a[i]
			i++
		} else {
			count += int64(mid - i)
			tmp[k] = a[j]
			j++
		}
		k++
	}
	for i < mid {
		tmp[k] = a[i]
		i++
		k++
	}
	for j < n {
		tmp[k] = a[j]
		j++
		k++
	}
	copy(a, tmp[:n])
	return count
}

func Isqrt(n int64) (int64, error) {
	if n < 0 {
		return 0, ErrDomain
	}
	var res int64
	v := n
	bit := isqrtTop
	for bit > v {
		bit >>= 2
	}
	for bit != 0 {
		if v >= res+bit {
			v -= res + bit
			res = (res >> 1) + bit
		} else {
			res >>= 1
		}
		bit >>= 2
	}
	return res, nil
}
