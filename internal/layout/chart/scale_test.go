package chart_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/chart"
)

func steps(from, step, count int64) []int64 {
	out := make([]int64, count)
	for i := range out {
		out[i] = from + int64(i)*step
	}
	return out
}

func TestTicksFollowTheD3Rule(t *testing.T) {
	for _, c := range []struct {
		name   string
		lo, hi int64
		want   []int64
	}{
		{"unit steps", 0, 10000, steps(0, 1000, 11)},
		{"ten per tick", 0, 100000, steps(0, 10000, 11)},
		{"twos", 0, 198200, steps(0, 20000, 10)},
		{"fives", 4000000, 11000000, steps(4000000, 500000, 15)},
		{"negative twos", -10000, 10000, steps(-10000, 2000, 11)},
		{"fractional fives", 0, 500, steps(0, 50, 11)},
		{"sub unit domain", 0, 5, steps(0, 1, 6)},
		{"misaligned start rounds up", 1500, 9500, steps(2000, 1000, 8)},
		{"no span", 7000, 7000, []int64{7000}},
		{"reversed", 10000, 0, steps(10000, -1000, 11)},
	} {
		got, capped, err := chart.Ticks(c.lo, c.hi)
		require.NoError(t, err, c.name)
		require.False(t, capped, c.name)
		require.Equal(t, c.want, got, c.name)
	}
}

func TestTickCountNeverExceedsTwiceTheRequest(t *testing.T) {
	for lo := int64(-50000); lo < 50000; lo += 7919 {
		for span := int64(1); span < 3_000_000_000; span = span*3 + 1 {
			ticks, capped, err := chart.Ticks(lo, lo+span)
			require.NoError(t, err)
			require.False(t, capped)
			require.LessOrEqual(t, len(ticks), 21)
			require.GreaterOrEqual(t, ticks[0], lo)
			require.LessOrEqual(t, ticks[len(ticks)-1], lo+span)
		}
	}
}

func TestTicksRejectSpansAboveInt32(t *testing.T) {
	_, _, err := chart.Ticks(0, int64(geom.I32Max)+1)
	require.ErrorIs(t, err, chart.ErrOverflow)
}

func TestFormatNumberTrimsTrailingZeros(t *testing.T) {
	for value, want := range map[int64]string{0: "0", 1500: "1.5", -2500: "-2.5", 5: "0.005", -5: "-0.005", 100000: "100", 1100: "1.1", 120: "0.12"} {
		require.Equal(t, want, chart.FormatNumber(value))
	}
}

func TestLinearMapFloorsAndHandlesReversedDomains(t *testing.T) {
	forward := chart.Linear{D0: 0, D1: 3, R0: 0, R1: 10}
	require.Equal(t, int64(3), forward.Map(1))
	require.Equal(t, int64(10), forward.Map(3))
	reversed := chart.Linear{D0: 3, D1: 0, R0: 0, R1: 10}
	require.Equal(t, int64(6), reversed.Map(1))
	require.Equal(t, int64(-4), chart.Linear{D0: 0, D1: 3, R0: 0, R1: -10}.Map(1))
}

func TestLinearMapOfAZeroWidthDomainIsTheRangeMidpoint(t *testing.T) {
	require.Equal(t, int64(4), chart.Linear{D0: 5, D1: 5, R0: 0, R1: 9}.Map(5))
	require.Equal(t, int64(-2), chart.Linear{D0: 5, D1: 5, R0: -3, R1: 0}.Map(77))
}

func TestBandPositionsAreEvenlySpacedAndSingleCategoryCentres(t *testing.T) {
	require.Equal(t, []int64{100, 103, 106, 110}, []int64{
		chart.BandPosition(0, 4, 100, 110), chart.BandPosition(1, 4, 100, 110),
		chart.BandPosition(2, 4, 100, 110), chart.BandPosition(3, 4, 100, 110),
	})
	require.Equal(t, int64(105), chart.BandPosition(0, 1, 100, 110))
	require.Equal(t, int64(100), chart.BandPosition(0, 2, 100, 110))
	require.Equal(t, int64(110), chart.BandPosition(1, 2, 100, 110))
}

func TestClampOrdersItsBounds(t *testing.T) {
	require.Equal(t, int64(5), chart.Clamp(9, 5, 2))
	require.Equal(t, int64(2), chart.Clamp(-9, 5, 2))
	require.Equal(t, int64(3), chart.Clamp(3, 2, 5))
}
