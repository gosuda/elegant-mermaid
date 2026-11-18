package geom

import (
	"errors"
	"math"
	"math/big"
	"testing"

	"github.com/stretchr/testify/require"
)

type rng struct {
	s uint32
}

func newRng(caseIndex int) *rng {
	r := &rng{s: uint32(caseIndex + 1)}
	for range 8 {
		r.next()
	}
	return r
}

func (r *rng) next() uint32 {
	r.s ^= r.s << 13
	r.s ^= r.s >> 17
	r.s ^= r.s << 5
	return r.s
}

var boundary = [5]int32{-2147483648, -1, 0, 1, 2147483647}

func (r *rng) draw(lo, hi int32) int32 {
	s := r.next()
	if s%16 == 0 {
		b := boundary[r.next()%5]
		if b >= lo && b <= hi {
			return b
		}
	}
	return lo + int32(r.next()%uint32(hi-lo+1))
}

func (r *rng) smallRect() Rect {
	return Rect{X: r.draw(-6, 6), Y: r.draw(-6, 6), W: r.draw(-2, 5), H: r.draw(-2, 5)}
}

func (r *rng) point() Point {
	return Point{X: r.draw(-6, 6), Y: r.draw(-6, 6)}
}

func (r *rng) axis() Axis {
	if r.next()%2 == 0 {
		return AxisX
	}
	return AxisY
}

func (r *rng) smallSegment() Segment {
	a := r.point()
	b := r.point()
	if r.next()%2 == 0 {
		b.Y = a.Y
	} else {
		b.X = a.X
	}
	return Segment{A: a, B: b}
}

func TestFloorDivMod(t *testing.T) {
	r := newRng(0)
	for range 2000 {
		a := int64(r.draw(-100000, 100000))
		b := int64(r.draw(1, 1000))
		q := FloorDiv(a, b)
		m := FloorMod(a, b)
		if m < 0 || m >= b {
			t.Fatalf("FloorMod(%d,%d)=%d out of [0,%d)", a, b, m, b)
		}
		if q*b+m != a {
			t.Fatalf("FloorDiv/FloorMod identity failed for %d,%d", a, b)
		}
	}
	if FloorDiv(-7, 2) != -4 || FloorMod(-7, 2) != 1 {
		t.Fatal("negative dividend floor rules broken")
	}
}

func rectCorners(r Rect) [4]Point {
	return [4]Point{
		{r.X, r.Y}, {r.X + r.W, r.Y}, {r.X + r.W, r.Y + r.H}, {r.X, r.Y + r.H},
	}
}

func containsCorners(outer, inner Rect) bool {
	for _, c := range rectCorners(inner) {
		if c.X < outer.X || c.X > outer.X+outer.W || c.Y < outer.Y || c.Y > outer.Y+outer.H {
			return false
		}
	}
	return true
}

func TestContains(t *testing.T) {
	r := newRng(1)
	for i := range 2000 {
		a := r.smallRect()
		b := r.smallRect()
		got, err := Contains(a, b)
		if !rectValid(a) || !rectValid(b) {
			if !errors.Is(err, ErrDomain) {
				t.Fatalf("case %d: expected domain error, got %v", i, err)
			}
			continue
		}
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		if got != containsCorners(a, b) {
			t.Fatalf("case %d: Contains(%v,%v)=%v", i, a, b, got)
		}
	}
}

func TestIntersects(t *testing.T) {
	r := newRng(2)
	for i := range 2000 {
		a := r.smallRect()
		b := r.smallRect()
		got, err := Intersects(a, b)
		if !rectValid(a) || !rectValid(b) {
			if !errors.Is(err, ErrDomain) {
				t.Fatalf("case %d: expected domain error, got %v", i, err)
			}
			continue
		}
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		want := intersectsScan(a, b)
		if got != want {
			t.Fatalf("case %d: Intersects(%v,%v)=%v want %v", i, a, b, got, want)
		}
	}
}

func intersectsScan(a, b Rect) bool {
	ax0, ax1 := 2*int64(a.X), 2*(int64(a.X)+int64(a.W))
	ay0, ay1 := 2*int64(a.Y), 2*(int64(a.Y)+int64(a.H))
	bx0, bx1 := 2*int64(b.X), 2*(int64(b.X)+int64(b.W))
	by0, by1 := 2*int64(b.Y), 2*(int64(b.Y)+int64(b.H))
	for px := ax0 + 1; px < ax1; px++ {
		if px <= bx0 || px >= bx1 {
			continue
		}
		for py := ay0 + 1; py < ay1; py++ {
			if py > by0 && py < by1 {
				return true
			}
		}
	}
	return false
}

func segPointsOnOpen(s Segment, px, py int64) bool {
	if s.A.Y == s.B.Y {
		if py != 2*int64(s.A.Y) {
			return false
		}
		lo, hi := segXSpan(s)
		return 2*lo < px && px < 2*hi
	}
	if px != 2*int64(s.A.X) {
		return false
	}
	lo, hi := segYSpan(s)
	return 2*lo < py && py < 2*hi
}

func segmentsCrossScan(s, t Segment) bool {
	if s.A == s.B || t.A == t.B {
		return false
	}
	lo := min(min(int64(s.A.X), int64(s.B.X)), min(int64(t.A.X), int64(t.B.X)))
	hi := max(max(int64(s.A.X), int64(s.B.X)), max(int64(t.A.X), int64(t.B.X)))
	vlo := min(min(int64(s.A.Y), int64(s.B.Y)), min(int64(t.A.Y), int64(t.B.Y)))
	vhi := max(max(int64(s.A.Y), int64(s.B.Y)), max(int64(t.A.Y), int64(t.B.Y)))
	for px := 2 * lo; px <= 2*hi; px++ {
		for py := 2 * vlo; py <= 2*vhi; py++ {
			if segPointsOnOpen(s, px, py) && segPointsOnOpen(t, px, py) {
				return true
			}
		}
	}
	return false
}

func TestSegmentsCross(t *testing.T) {
	r := newRng(3)
	for i := range 2000 {
		s := r.smallSegment()
		u := r.smallSegment()
		got, err := SegmentsCross(s, u)
		if !axisAligned(s) || !axisAligned(u) {
			if !errors.Is(err, ErrDomain) {
				t.Fatalf("case %d: expected domain error, got %v", i, err)
			}
			continue
		}
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		want := segmentsCrossScan(s, u)
		if got != want {
			t.Fatalf("case %d: SegmentsCross(%v,%v)=%v want %v", i, s, u, got, want)
		}
	}
}

func TestPolylineHitsRectHandCases(t *testing.T) {
	cases := []struct {
		p    []Point
		r    Rect
		want bool
	}{
		{[]Point{{0, 5}, {10, 5}}, Rect{2, 3, 4, 4}, true},
		{[]Point{{0, 5}, {5, 5}}, Rect{5, 3, 4, 4}, false},
		{[]Point{{0, 0}, {2, 2}}, Rect{2, 0, 2, 2}, false},
		{[]Point{{0, 0}, {10, 10}}, Rect{3, 3, 0, 5}, false},
		{[]Point{{5, 5}}, Rect{0, 0, 10, 10}, true},
		{[]Point{{0, 5}}, Rect{0, 0, 10, 10}, false},
		{[]Point{{20, 20}}, Rect{0, 0, 10, 10}, false},
		{[]Point{{5, -5}, {5, 5}}, Rect{0, 0, 10, 3}, true},
		{[]Point{{-5, -5}, {-1, -1}}, Rect{0, 0, 10, 10}, false},
		{[]Point{{0, 0}, {2, 2}}, Rect{1, 1, 2, 2}, true},
		{[]Point{{5, 5}, {5, 5}}, Rect{0, 0, 10, 10}, true},
		{[]Point{{-5, 0}, {5, 0}}, Rect{0, 0, 10, 10}, false},
		{[]Point{{1, 1}, {3, 3}}, Rect{1, 1, 2, 2}, true},
		{[]Point{{0, 0}, {1, 1}, {5, 5}}, Rect{2, 2, 1, 1}, true},
		{nil, Rect{0, 0, 10, 10}, false},
	}
	for i, c := range cases {
		got, err := PolylineHitsRect(c.p, c.r)
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		if got != c.want {
			t.Fatalf("case %d: PolylineHitsRect(%v,%v)=%v want %v", i, c.p, c.r, got, c.want)
		}
		if got != quarterScan(c.p, c.r) {
			t.Fatalf("case %d: quarter-lattice scan disagrees with %v", i, got)
		}
	}
}

func quarterScan(p []Point, r Rect) bool {
	if r.W == 0 || r.H == 0 {
		return false
	}
	if len(p) < 2 {
		return len(p) == 1 && pointInOpen(p[0], r)
	}
	for i := range len(p) - 1 {
		if segQuarterHit(p[i], p[i+1], r) {
			return true
		}
	}
	return false
}

func segQuarterHit(a, b Point, r Rect) bool {
	if a == b {
		return pointInOpen(a, r)
	}
	x0, y0 := 4*int64(r.X), 4*int64(r.Y)
	x1, y1 := 4*(int64(r.X)+int64(r.W)), 4*(int64(r.Y)+int64(r.H))
	for px := x0 + 1; px < x1; px++ {
		for py := y0 + 1; py < y1; py++ {
			if pointOnClosedSeg(a, b, px, py) {
				return true
			}
		}
	}
	return false
}

func pointOnClosedSeg(a, b Point, px, py int64) bool {
	ax, ay := 4*int64(a.X), 4*int64(a.Y)
	bx, by := 4*int64(b.X), 4*int64(b.Y)
	if (bx-ax)*(py-ay)-(by-ay)*(px-ax) != 0 {
		return false
	}
	return px >= min(ax, bx) && px <= max(ax, bx) && py >= min(ay, by) && py <= max(ay, by)
}

func TestPolylineHitsRectRandom(t *testing.T) {
	r := newRng(4)
	for i := range 2000 {
		n := int(r.next() % 4)
		p := make([]Point, n)
		for j := range n {
			p[j] = r.point()
		}
		rect := r.smallRect()
		got, err := PolylineHitsRect(p, rect)
		if !rectValid(rect) {
			if !errors.Is(err, ErrDomain) {
				t.Fatalf("case %d: expected domain error, got %v", i, err)
			}
			continue
		}
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		want := clipScan(p, rect)
		if got != want {
			t.Fatalf("case %d: PolylineHitsRect(%v,%v)=%v want %v", i, p, rect, got, want)
		}
	}
}

func clipScan(p []Point, r Rect) bool {
	if r.W == 0 || r.H == 0 {
		return false
	}
	if len(p) < 2 {
		return len(p) == 1 && pointInOpen(p[0], r)
	}
	for i := range len(p) - 1 {
		if segClipHit(p[i], p[i+1], r) {
			return true
		}
	}
	return false
}

func segClipHit(a, b Point, r Rect) bool {
	if pointInOpen(a, r) || pointInOpen(b, r) {
		return true
	}
	dx := big.NewRat(int64(b.X)-int64(a.X), 1)
	dy := big.NewRat(int64(b.Y)-int64(a.Y), 1)
	loX, hiX, okX := strictBounds(dx, int64(a.X), int64(r.X), int64(r.X)+int64(r.W))
	loY, hiY, okY := strictBounds(dy, int64(a.Y), int64(r.Y), int64(r.Y)+int64(r.H))
	if !okX || !okY {
		return false
	}
	lo := ratMax(big.NewRat(0, 1), ratMax(loX, loY))
	hi := ratMin(big.NewRat(1, 1), ratMin(hiX, hiY))
	return lo.Cmp(hi) < 0
}

func strictBounds(d *big.Rat, start, lo, hi int64) (*big.Rat, *big.Rat, bool) {
	if d.Sign() == 0 {
		if start <= lo || start >= hi {
			return nil, nil, false
		}
		return big.NewRat(0, 1), big.NewRat(1, 1), true
	}
	l := new(big.Rat).Sub(big.NewRat(lo, 1), big.NewRat(start, 1))
	h := new(big.Rat).Sub(big.NewRat(hi, 1), big.NewRat(start, 1))
	l.Quo(l, d)
	h.Quo(h, d)
	if d.Sign() < 0 {
		l, h = h, l
	}
	return l, h, true
}

func ratMax(a, b *big.Rat) *big.Rat {
	if a.Cmp(b) >= 0 {
		return a
	}
	return b
}

func ratMin(a, b *big.Rat) *big.Rat {
	if a.Cmp(b) <= 0 {
		return a
	}
	return b
}

func naiveInversions(xs []int32) int64 {
	var n int64
	for i := range len(xs) {
		for j := i + 1; j < len(xs); j++ {
			if xs[i] > xs[j] {
				n++
			}
		}
	}
	return n
}

func TestCountInversions(t *testing.T) {
	r := newRng(5)
	for i := range 2000 {
		n := int(r.next() % 40)
		xs := make([]int32, n)
		for j := range n {
			xs[j] = r.draw(-50, 50)
		}
		got, err := CountInversions(xs)
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		if int64(got) != naiveInversions(xs) {
			t.Fatalf("case %d: CountInversions=%d want %d", i, got, naiveInversions(xs))
		}
	}
	descending := make([]int32, 70000)
	for i := range descending {
		descending[i] = int32(len(descending) - i)
	}
	if _, err := CountInversions(descending); !errors.Is(err, ErrOverflow) {
		t.Fatal("expected overflow on large inversion count")
	}
}

func TestIsqrt(t *testing.T) {
	r := newRng(6)
	for i := range 2000 {
		n := int64(r.draw(0, 100000))
		n = n*n + int64(r.draw(0, 200))
		got, err := Isqrt(n)
		if err != nil {
			t.Fatalf("case %d: %v", i, err)
		}
		if !isqrtExact(n, got) {
			t.Fatalf("case %d: Isqrt(%d)=%d", i, n, got)
		}
	}
	for _, n := range []int64{0, 1, 2, 3, 4, 1 << 62, math.MaxInt64} {
		got, err := Isqrt(n)
		if err != nil {
			t.Fatalf("Isqrt(%d): %v", n, err)
		}
		if !isqrtExact(n, got) {
			t.Fatalf("Isqrt(%d)=%d", n, got)
		}
	}
	if _, err := Isqrt(-1); !errors.Is(err, ErrDomain) {
		t.Fatal("expected domain error")
	}
}

type compactCase struct {
	index int
	axis  Axis
	gap   int32
	items []Rect
}

func TestCompactOracle(t *testing.T) {
	r := newRng(7)
	for i := range 2000 {
		c := compactCase{index: i, axis: r.axis(), gap: r.draw(-2, 20), items: make([]Rect, int(r.next()%6))}
		for j := range c.items {
			c.items[j] = Rect{X: r.draw(-6, 6), Y: r.draw(-6, 6), W: r.draw(0, 5), H: r.draw(0, 5)}
		}
		checkCompactCase(t, c)
	}
}

func checkCompactCase(t *testing.T, c compactCase) {
	t.Helper()
	out, err := Compact(c.axis, c.gap, c.items)
	if c.gap < 0 {
		if !errors.Is(err, ErrDomain) {
			t.Fatalf("case %d: expected domain, got %v", c.index, err)
		}
		return
	}
	if err != nil {
		t.Fatalf("case %d: %v", c.index, err)
	}
	var prevEnd int64
	for j, got := range out {
		pos, size := compactAxisOf(c.items[j], c.axis)
		if j > 0 && pos < prevEnd {
			pos = prevEnd
		}
		prevEnd = pos + size + int64(c.gap)
		if want := compactWant(c.items[j], c.axis, pos); got != want {
			t.Fatalf("case %d: item %d got %v want %v", c.index, j, got, want)
		}
	}
}

func compactAxisOf(r Rect, axis Axis) (int64, int64) {
	if axis == AxisY {
		return int64(r.Y), int64(r.H)
	}
	return int64(r.X), int64(r.W)
}

func compactWant(r Rect, axis Axis, pos int64) Rect {
	if axis == AxisY {
		r.Y = int32(pos)
	} else {
		r.X = int32(pos)
	}
	return r
}

func isqrtExact(n int64, m int64) bool {
	return m*m <= n && n/(m+1) < m+1
}

func TestOperationErrors(t *testing.T) {
	invalid := Rect{0, 0, -1, 0}
	{
		_, err := Translate(invalid, 1, 1)
		require.ErrorIs(t, err, ErrDomain, "translate with an invalid rect must fail with ErrDomain")
	}
	{
		_, err := Translate(Rect{0, 0, 1, 1}, math.MaxInt32, 0)
		require.ErrorIs(t, err, ErrOverflow, "translate past the int32 edge must fail with ErrOverflow")
	}
	{
		_, err := Translate(invalid, math.MaxInt32, 0)
		require.ErrorIs(t, err, ErrDomain, "an invalid rect must fail with ErrDomain before the overflow is reached")
	}
	{
		_, err := Inflate(invalid, 1)
		require.ErrorIs(t, err, ErrDomain, "inflate with an invalid rect must fail with ErrDomain")
	}
	{
		_, err := Inflate(Rect{0, 0, 4, 4}, -3)
		require.ErrorIs(t, err, ErrDomain, "inflate that would produce a negative size must fail with ErrDomain")
	}
	{
		_, err := Inflate(Rect{2147483646, 0, 1, 1}, 1)
		require.ErrorIs(t, err, ErrOverflow, "inflate past the int32 edge must fail with ErrOverflow")
	}
	{
		_, err := Inflate(Rect{2147483646, 0, 1, 1}, -5)
		require.ErrorIs(t, err, ErrDomain, "a negative inflate size must fail with ErrDomain before the overflow is reached")
	}
	{
		_, err := Union(Rect{2147483647, 0, 0, 0}, Rect{-2147483648, 0, 0, 0})
		require.ErrorIs(t, err, ErrOverflow, "a union spanning the full int32 range must fail with ErrOverflow")
	}
	{
		_, err := Union(invalid, Rect{0, 0, 0, 0})
		require.ErrorIs(t, err, ErrDomain, "union with an invalid rect must fail with ErrDomain")
	}
	{
		_, err := Intersects(invalid, Rect{0, 0, 0, 0})
		require.ErrorIs(t, err, ErrDomain, "intersects with an invalid rect must fail with ErrDomain")
	}
	{
		_, err := Contains(Rect{0, 0, 0, 0}, invalid)
		require.ErrorIs(t, err, ErrDomain, "contains with an invalid inner rect must fail with ErrDomain")
	}
	{
		_, err := PlaceAfter(AxisX, Rect{2147483647, 0, 0, 0}, -1, Size{1, 1})
		require.ErrorIs(t, err, ErrDomain, "place_after with a negative gap must fail with ErrDomain")
	}
	{
		_, err := PlaceAfter(AxisX, Rect{0, 0, 0, 0}, 0, Size{-1, 1})
		require.ErrorIs(t, err, ErrDomain, "place_after with a negative size must fail with ErrDomain")
	}
	{
		_, err := PlaceAfter(AxisX, Rect{2147483647, 0, 0, 0}, 0, Size{1, 1})
		require.ErrorIs(t, err, ErrOverflow, "place_after past the int32 edge must fail with ErrOverflow")
	}
	{
		_, err := PlaceAfter(AxisX, invalid, -1, Size{-1, 1})
		require.ErrorIs(t, err, ErrDomain, "invalid place_after inputs must fail with ErrDomain before the overflow is reached")
	}
	{
		_, err := Compact(AxisX, -1, nil)
		require.ErrorIs(t, err, ErrDomain, "compact with a negative gap must fail with ErrDomain")
	}
	{
		_, err := Compact(AxisX, 1, []Rect{invalid})
		require.ErrorIs(t, err, ErrDomain, "compact with an invalid item must fail with ErrDomain")
	}
	{
		_, err := Compact(AxisX, 1, []Rect{{0, 0, 2147483647, 0}, {0, 0, 1, 1}})
		require.ErrorIs(t, err, ErrOverflow, "compact past the int32 edge must fail with ErrOverflow")
	}
	diag := Segment{A: Point{0, 0}, B: Point{1, 1}}
	{
		_, err := SegmentsCross(diag, diag)
		require.ErrorIs(t, err, ErrDomain, "segments_cross with a diagonal segment must fail with ErrDomain")
	}
	{
		_, err := PolylineHitsRect([]Point{{0, 0}}, invalid)
		require.ErrorIs(t, err, ErrDomain, "polyline_hits_rect with an invalid rect must fail with ErrDomain")
	}
	{
		_, err := PolylineHitsRect([]Point{{1 << 30, 0}}, Rect{0, 0, 1, 1})
		require.ErrorIs(t, err, ErrDomain, "a point outside the coordinate limit must fail with ErrDomain")
	}
	{
		_, err := PolylineHitsRect([]Point{{0, 0}}, Rect{0, 0, (1 << 29) + 1, 0})
		require.ErrorIs(t, err, ErrDomain, "a rect edge outside the coordinate limit must fail with ErrDomain")
	}
}

func TestSinQ15(t *testing.T) {
	if SinQ15(0) != 0 {
		t.Fatal("SinQ15(0) != 0")
	}
	if SinQ15(16384) != 32768 {
		t.Fatal("SinQ15(16384) != 32768")
	}
	if SinQ15(-16384) != -32768 {
		t.Fatal("SinQ15(-16384) != -32768")
	}
	r := newRng(8)
	for i := range 2000 {
		a := r.draw(-200000, 200000)
		v := SinQ15(a)
		if v < -32768 || v > 32768 {
			t.Fatalf("case %d: SinQ15(%d)=%d out of range", i, a, v)
		}
		if SinQ15(a+32768) != -v {
			t.Fatalf("case %d: half-turn antisymmetry broken at %d", i, a)
		}
		if CosQ15(a) != SinQ15(a+16384) {
			t.Fatalf("case %d: CosQ15 identity broken at %d", i, a)
		}
	}
}
