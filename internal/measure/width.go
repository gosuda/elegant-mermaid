package measure

import (
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type Role uint8

const (
	RoleBody Role = iota
	RoleLabel
	RoleTitle
)

type Weight uint8

const (
	WeightRegular  Weight = 0
	WeightSemiBold Weight = 1
)

type Profile uint8

const (
	ProfileVector Profile = iota
	ProfileCell
)

const (
	defaultWrapVector int32 = 12800
	defaultWrapCell   int32 = 32
)

func (r Role) SizePx() int32 {
	if r == RoleTitle {
		return 16
	}
	return 14
}

func (r Role) LineHeightPx() int32 {
	if r == RoleTitle {
		return 24
	}
	return 20
}

func (r Role) Weight() Weight {
	if r == RoleBody {
		return WeightRegular
	}
	return WeightSemiBold
}

func Upem(w Weight) (int32, error) {
	if int(w) >= len(gen.AdvancesUpem) {
		return 0, geom.ErrDomain
	}
	return gen.AdvancesUpem[w], nil
}

func Advance(w Weight, cp rune) (int32, error) {
	upem, err := Upem(w)
	if err != nil {
		return 0, err
	}
	if units, ok := advanceUnits(uint8(w), cp); ok {
		return int32(units), nil
	}
	if scalarWidth(cp) == 2 {
		return upem, nil
	}
	return int32(geom.FloorDiv(6*int64(upem)+5, 10)), nil
}

func AdvanceSum(s string, w Weight) (int64, error) {
	upem, err := Upem(w)
	if err != nil {
		return 0, err
	}
	fallbackWide := int64(upem)
	fallbackNarrow := geom.FloorDiv(6*int64(upem)+5, 10)
	var sum int64
	for _, cp := range s {
		if units, ok := advanceUnits(uint8(w), cp); ok {
			sum += int64(units)
			continue
		}
		if scalarWidth(cp) == 2 {
			sum += fallbackWide
			continue
		}
		sum += fallbackNarrow
	}
	return sum, nil
}

func VectorWidth(s string, sizePx int32, w Weight) (int32, error) {
	if sizePx < 0 {
		return 0, geom.ErrDomain
	}
	if s == "" {
		return 0, nil
	}
	upem, err := Upem(w)
	if err != nil {
		return 0, err
	}
	sum, err := AdvanceSum(s, w)
	if err != nil {
		return 0, err
	}
	product, err := mul64(sum, int64(sizePx)*64)
	if err != nil {
		return 0, err
	}
	return checkedI32(CeilDiv(product, int64(upem)))
}

func FontFamilyFactor(w int32) (int32, error) {
	return checkedI32(geom.FloorDiv(int64(w)*108, 100))
}

func (r Role) Width(s string) (int32, error) {
	return VectorWidth(s, r.SizePx(), r.Weight())
}

func WrapTarget(profile Profile, kindTarget, maxWidth int32) int32 {
	if kindTarget > 0 {
		return kindTarget
	}
	if maxWidth > 0 {
		return maxWidth
	}
	if profile == ProfileCell {
		return defaultWrapCell
	}
	return defaultWrapVector
}

func (m Metric) TextWidth(s string) (int32, error) {
	if m.Profile == ProfileCell {
		return CellWidth(s)
	}
	w, err := VectorWidth(s, m.SizePx, m.Weight)
	if err != nil {
		return 0, err
	}
	if m.FontFamily {
		return FontFamilyFactor(w)
	}
	return w, nil
}

type Metric struct {
	Profile    Profile
	SizePx     int32
	Weight     Weight
	FontFamily bool
}

func ForRole(r Role) Metric {
	return Metric{Profile: ProfileVector, SizePx: r.SizePx(), Weight: r.Weight()}
}

func CellMetric() Metric {
	return Metric{Profile: ProfileCell}
}

func CeilDiv(a, b int64) int64 {
	return geom.FloorDiv(a+b-1, b)
}

func RoundHalfUp(a, b int64) int64 {
	return geom.FloorDiv(2*a+b, 2*b)
}

func mul64(a, b int64) (int64, error) {
	if a == 0 || b == 0 {
		return 0, nil
	}
	p := a * b
	if p/b != a {
		return 0, geom.ErrOverflow
	}
	return p, nil
}

func checkedI32(v int64) (int32, error) {
	if v < int64(geom.I32Min) || v > int64(geom.I32Max) {
		return 0, geom.ErrOverflow
	}
	return int32(v), nil
}
