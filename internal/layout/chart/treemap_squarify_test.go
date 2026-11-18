package chart

import (
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
)

type treemapTestXorshift32 uint32

func (x *treemapTestXorshift32) next() uint32 {
	v := uint32(*x)
	v ^= v << 13
	v ^= v >> 17
	v ^= v << 5
	*x = treemapTestXorshift32(v)
	return v
}

func (x *treemapTestXorshift32) between(lo, hi int64) int64 {
	return lo + int64(x.next())%(hi-lo+1)
}

func bigOf(v int64) *big.Int { return big.NewInt(v) }

func bigShift(v int64, n uint) *big.Int { return new(big.Int).Lsh(bigOf(v), n) }

func bigFloor(n, d *big.Int) *big.Int { return new(big.Int).Div(n, d) }

func oracleRowAspect(largest, smallest, sum int64, alpha *big.Int) *big.Int {
	beta := new(big.Int).Mul(bigOf(sum), bigOf(sum))
	beta.Mul(beta, alpha)
	left := bigFloor(bigShift(largest, 80), beta)
	right := bigFloor(beta, bigOf(smallest))
	if left.Cmp(right) >= 0 {
		return left
	}
	return right
}

func oracleRound(a, b int64) int64 { return bigFloor(bigOf(2*a+b), bigOf(2*b)).Int64() }

func oracleGrow(values []int64, end int, sum int64, alpha *big.Int) (int, int64) {
	smallest, largest, total := sum, sum, sum
	aspect := oracleRowAspect(largest, smallest, total, alpha)
	for end < len(values) && values[end] != 0 {
		v := values[end]
		next := oracleRowAspect(max(largest, v), min(smallest, v), total+v, alpha)
		if next.Cmp(aspect) > 0 {
			break
		}
		aspect, total, smallest, largest = next, total+v, min(smallest, v), max(largest, v)
		end++
	}
	return end, total
}

func oracleRow(values []int64, first int, area tile, remaining, rho int64) (end int, sum int64) {
	end = first
	for {
		sum = values[end]
		end++
		if sum != 0 || end == len(values) {
			break
		}
	}
	dx, dy := area.x1-area.x0, area.y1-area.y0
	if sum == 0 {
		return end, 0
	}
	if min(dx, dy) == 0 {
		return len(values), remaining
	}
	den := new(big.Int).Mul(bigOf(min(dx, dy)), bigOf(remaining))
	den.Mul(den, bigOf(rho))
	return oracleGrow(values, end, sum, bigFloor(bigShift(max(dx, dy), 70), den))
}

type oracleStripTotals struct{ sum, remaining int64 }

func oracleStrip(cells []tile, values []int64, area tile, totals oracleStripTotals) tile {
	dx, dy := area.x1-area.x0, area.y1-area.y0
	dice := dx < dy
	along, across := dx, dy
	if !dice {
		along, across = dy, dx
	}
	thickness := across
	if totals.sum > 0 && totals.remaining > 0 {
		thickness = oracleRound(across*totals.sum, totals.remaining)
	}
	var cumulative, previous int64
	for k, v := range values {
		cumulative += v
		var boundary int64
		if totals.sum > 0 {
			boundary = oracleRound(along*cumulative, totals.sum)
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

func oracleSquarify(values []int64, area tile, rho int64) []tile {
	cells := make([]tile, len(values))
	var remaining int64
	for _, v := range values {
		remaining += v
	}
	for first := 0; first < len(values); {
		end, sum := oracleRow(values, first, area, remaining, rho)
		area = oracleStrip(cells[first:end], values[first:end], area, oracleStripTotals{sum, remaining})
		remaining -= sum
		first = end
	}
	return cells
}

func randomTreemapCase(index uint32) ([]int64, tile) {
	rng := treemapTestXorshift32(index + 1)
	for range 8 {
		rng.next()
	}
	count := int(rng.between(1, 40))
	values := make([]int64, count)
	for i := range values {
		switch rng.next() % 6 {
		case 0:
			values[i] = 0
		case 1:
			values[i] = rng.between(1, 1<<24/int64(count))
		default:
			values[i] = rng.between(1, 1000)
		}
	}
	slicesSortDescending(values)
	area := tile{x0: rng.between(0, 5000), y0: rng.between(0, 5000)}
	area.x1, area.y1 = area.x0+rng.between(0, 70000), area.y0+rng.between(0, 40000)
	return values, area
}

func slicesSortDescending(values []int64) {
	for i := 1; i < len(values); i++ {
		for j := i; j > 0 && values[j] > values[j-1]; j-- {
			values[j], values[j-1] = values[j-1], values[j]
		}
	}
}

const testRho = 1737350766

func TestSquarifyMatchesBigIntegerOracle(t *testing.T) {
	for index := range uint32(500) {
		values, area := randomTreemapCase(index)
		got, capped, err := squarify(values, area, testRho, 2000)
		require.NoError(t, err)
		require.False(t, capped)
		require.Equal(t, oracleSquarify(values, area, testRho), got, "case %d", index)
	}
}

func TestSquarifyPartitionsTheAreaExactly(t *testing.T) {
	for index := range uint32(500) {
		values, area := randomTreemapCase(index)
		cells, _, err := squarify(values, area, testRho, 2000)
		require.NoError(t, err)
		var total, nonZero int64
		for k, c := range cells {
			require.GreaterOrEqual(t, c.x0, area.x0, "case %d cell %d", index, k)
			require.GreaterOrEqual(t, c.y0, area.y0, "case %d cell %d", index, k)
			require.LessOrEqual(t, c.x1, area.x1, "case %d cell %d", index, k)
			require.LessOrEqual(t, c.y1, area.y1, "case %d cell %d", index, k)
			require.LessOrEqual(t, c.x0, c.x1)
			require.LessOrEqual(t, c.y0, c.y1)
			total += (c.x1 - c.x0) * (c.y1 - c.y0)
			nonZero += values[k]
		}
		if nonZero > 0 {
			require.Equal(t, (area.x1-area.x0)*(area.y1-area.y0), total, "case %d", index)
		}
		for a := range cells {
			for b := a + 1; b < len(cells); b++ {
				require.False(t, tilesOverlap(cells[a], cells[b]), "case %d cells %d %d", index, a, b)
			}
		}
	}
}

func tilesOverlap(a, b tile) bool {
	return max(a.x0, b.x0) < min(a.x1, b.x1) && max(a.y0, b.y0) < min(a.y1, b.y1)
}

func TestSquarifyKnownLayout(t *testing.T) {
	cells, _, err := squarify([]int64{6, 6, 4, 3, 2, 2, 1}, tile{0, 0, 600, 400}, testRho, 2000)
	require.NoError(t, err)
	require.Equal(t, []tile{{0, 0, 300, 200}, {0, 200, 300, 400}}, cells[:2])
	var total int64
	for _, c := range cells {
		total += (c.x1 - c.x0) * (c.y1 - c.y0)
	}
	require.Equal(t, int64(600*400), total)
}

func TestSquarifyFuelForcesTheLastRow(t *testing.T) {
	values := []int64{50, 30, 20, 10, 5, 3, 2, 1}
	cells, capped, err := squarify(values, tile{0, 0, 1000, 600}, testRho, 2)
	require.NoError(t, err)
	require.True(t, capped)
	var total int64
	for _, c := range cells {
		total += (c.x1 - c.x0) * (c.y1 - c.y0)
	}
	require.Equal(t, int64(1000*600), total)
	_, capped, err = squarify(values, tile{0, 0, 1000, 600}, testRho, 100)
	require.NoError(t, err)
	require.False(t, capped)
}

func TestSquarifyRejectsInvalidInput(t *testing.T) {
	_, _, err := squarify([]int64{-1}, tile{0, 0, 10, 10}, testRho, 10)
	require.ErrorIs(t, err, errDomain)
	_, _, err = squarify([]int64{1 << 32}, tile{0, 0, 10, 10}, testRho, 10)
	require.ErrorIs(t, err, errDomain)
	_, _, err = squarify([]int64{1}, tile{10, 0, 0, 10}, testRho, 10)
	require.ErrorIs(t, err, errDomain)
}

func TestSquarifyAllZeroValuesFillWithEmptyCells(t *testing.T) {
	cells, _, err := squarify([]int64{0, 0, 0}, tile{0, 0, 100, 50}, testRho, 10)
	require.NoError(t, err)
	require.Len(t, cells, 3)
	for _, c := range cells {
		require.Zero(t, (c.x1-c.x0)*(c.y1-c.y0))
	}
}

func TestNormalizeScalesLargeTotals(t *testing.T) {
	out, err := normalizeTreemap([]int64{1_000_000_000_000, 7_654_321_000}, 24)
	require.NoError(t, err)
	var total int64
	for _, v := range out {
		total += v
	}
	require.LessOrEqual(t, total, int64(1)<<24)
	require.Greater(t, out[0], out[1])
	require.Positive(t, out[1])
	same, err := normalizeTreemap([]int64{3, 4}, 24)
	require.NoError(t, err)
	require.Equal(t, []int64{3, 4}, same)
	_, err = normalizeTreemap([]int64{-1}, 24)
	require.ErrorIs(t, err, errDomain)
	_, err = normalizeTreemap([]int64{treemapRawCap + 1}, 24)
	require.ErrorIs(t, err, ErrOverflow)
}

func TestNormalizeMatchesBigIntegerFloor(t *testing.T) {
	for index := range uint32(200) {
		rng := treemapTestXorshift32(index + 1)
		raw := make([]int64, rng.between(1, 30))
		var total int64
		for i := range raw {
			raw[i] = rng.between(0, treemapRawCap/64)
			total += raw[i]
		}
		out, err := normalizeTreemap(raw, 24)
		require.NoError(t, err)
		for i, v := range raw {
			want := v
			if total > 1<<24 {
				want = bigFloor(new(big.Int).Mul(bigOf(v), bigOf(1<<24)), bigOf(total)).Int64()
			}
			require.Equal(t, want, out[i], "case %d", index)
		}
	}
}
