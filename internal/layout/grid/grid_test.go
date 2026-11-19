package grid

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var testParams = Params{Padding: 8, BendCost: 64, LineThickness: 0}

func leaf(parent int, span int32, w, h int32) Box {
	return Box{Parent: parent, Kind: KindLeaf, Span: span, Size: geom.Size{W: w, H: h}}
}

func composite(parent int, span, columns int32) Box {
	return Box{Parent: parent, Kind: KindComposite, Span: span, Columns: columns}
}

func space(parent int) Box { return Box{Parent: parent, Kind: KindSpace, Span: 1} }

func mustBlock(t *testing.T, in Input) Layout {
	t.Helper()
	out, err := Block(in, testParams)
	require.NoError(t, err)
	return out
}

func TestGridPositionsFollowColumns(t *testing.T) {
	in := Input{Columns: 3, Boxes: []Box{leaf(-1, 1, 40, 10), leaf(-1, 2, 100, 20), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10)}}
	out := mustBlock(t, in)
	const unit = 50
	require.Equal(t, geom.Rect{X: 8, Y: 8, W: unit, H: 20}, out.Rects[0])
	require.Equal(t, geom.Rect{X: 8 + (unit + 8), Y: 8, W: 2*unit + 8, H: 20}, out.Rects[1])
	require.Equal(t, geom.Rect{X: 8, Y: 8 + 20 + 8, W: unit, H: 10}, out.Rects[2])
	require.Equal(t, geom.Rect{X: 8 + (unit + 8), Y: 8 + 20 + 8, W: unit, H: 10}, out.Rects[3])
	require.Equal(t, geom.Size{W: 3*unit + 4*8, H: 20 + 10 + 3*8}, out.Canvas)
}

func TestSpanIsClippedToTheRestOfTheRow(t *testing.T) {
	in := Input{Columns: 2, Boxes: []Box{leaf(-1, 1, 10, 10), leaf(-1, 5, 10, 10)}}
	out := mustBlock(t, in)
	require.Equal(t, out.Rects[0].W, out.Rects[1].W)
	require.Equal(t, out.Rects[0].Y, out.Rects[1].Y)
}

func TestWideChildStartsANewRowWhenItDoesNotFit(t *testing.T) {
	in := Input{Columns: 3, Boxes: []Box{leaf(-1, 1, 10, 10), leaf(-1, 1, 10, 10), leaf(-1, 1, 10, 10), leaf(-1, 1, 10, 10)}}
	out := mustBlock(t, in)
	require.Equal(t, out.Rects[0].X, out.Rects[3].X)
	require.Greater(t, out.Rects[3].Y, out.Rects[0].Y)
}

func TestAutoColumnsPlaceOneRow(t *testing.T) {
	in := Input{Columns: 0, Boxes: []Box{leaf(-1, 1, 10, 10), leaf(-1, 1, 10, 30), leaf(-1, 2, 10, 10)}}
	out := mustBlock(t, in)
	for _, r := range out.Rects[:len(in.Boxes)] {
		require.Equal(t, int32(8), r.Y)
		require.Equal(t, int32(30), r.H)
	}
}

func TestSpaceTakesASlotButNoSize(t *testing.T) {
	in := Input{Columns: 2, Boxes: []Box{space(-1), leaf(-1, 1, 40, 10), leaf(-1, 1, 40, 10)}}
	out := mustBlock(t, in)
	require.Equal(t, out.Rects[0].X, out.Rects[2].X)
	require.Greater(t, out.Rects[1].X, out.Rects[0].X)
	require.Equal(t, int32(10), out.Rects[0].H)
}

func TestSpaceOnlyRowAddsNoHeight(t *testing.T) {
	in := Input{Columns: 1, Boxes: []Box{space(-1), leaf(-1, 1, 10, 10)}}
	out := mustBlock(t, in)
	require.Equal(t, int32(0), out.Rects[0].H)
	require.Equal(t, int32(8+0+8), out.Rects[1].Y)
}

func TestCompositeContainsItsChildren(t *testing.T) {
	in := Input{Columns: 2, Boxes: []Box{composite(-1, 1, 2), leaf(0, 1, 30, 10), leaf(0, 1, 30, 10), leaf(-1, 1, 20, 10)}}
	out := mustBlock(t, in)
	frame := out.Rects[0]
	for _, child := range out.Rects[1:3] {
		ok, err := geom.Contains(frame, child)
		require.NoError(t, err)
		require.True(t, ok)
	}
	require.Equal(t, out.Rects[1].Y, out.Rects[2].Y)
	require.Equal(t, frame.X+8, out.Rects[1].X)
}

func TestNestedCompositeInheritsRowHeight(t *testing.T) {
	in := Input{Columns: 2, Boxes: []Box{composite(-1, 1, 1), leaf(0, 1, 30, 10), leaf(0, 1, 30, 10), leaf(-1, 1, 20, 10)}}
	out := mustBlock(t, in)
	require.Equal(t, int32(10+10+3*8), out.Rects[0].H)
	require.Equal(t, out.Rects[0].H, out.Rects[3].H)
}

func TestSpanWidensCompositeColumnUnit(t *testing.T) {
	narrow := mustBlock(t, Input{Columns: 2, Boxes: []Box{leaf(-1, 2, 10, 10), leaf(-1, 1, 10, 10)}})
	wide := mustBlock(t, Input{Columns: 2, Boxes: []Box{leaf(-1, 2, 200, 10), leaf(-1, 1, 10, 10)}})
	require.Less(t, narrow.Canvas.W, wide.Canvas.W)
	require.Equal(t, wide.Rects[0].W, 2*wide.Rects[1].W+8)
}

func TestEmptyInputHasMarginsOnly(t *testing.T) {
	out := mustBlock(t, Input{})
	require.Equal(t, geom.Size{W: 8, H: 8}, out.Canvas)
	require.Empty(t, out.Rects[:len(out.Rects)-1])
}

func TestInvalidInputIsRejected(t *testing.T) {
	bad := []Input{
		{Boxes: []Box{leaf(0, 1, 1, 1)}},
		{Boxes: []Box{leaf(-1, 1, 1, 1), leaf(0, 1, 1, 1)}},
		{Boxes: []Box{leaf(-2, 1, 1, 1)}},
		{Boxes: []Box{leaf(-1, 1, -1, 1)}},
		{Boxes: []Box{leaf(-1, 1, 1, 1)}, Edges: []Edge{{From: 0, To: 3}}},
		{Boxes: []Box{leaf(-1, 1, 1, 1)}, Edges: []Edge{{From: 0, To: 0, Label: geom.Size{W: -1}}}},
	}
	for i, in := range bad {
		_, err := Block(in, testParams)
		require.ErrorIs(t, err, geom.ErrDomain, i)
	}
}

func TestOversizedCanvasOverflows(t *testing.T) {
	huge := int32(geom.CoordLimit - 4)
	_, err := Block(Input{Columns: 2, Boxes: []Box{leaf(-1, 1, huge, 10), leaf(-1, 1, huge, 10)}}, testParams)
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func TestTooManyTracksOverflow(t *testing.T) {
	boxes := make([]Box, maxTracks+1)
	for i := range boxes {
		boxes[i] = leaf(-1, 1, 1, 1)
	}
	_, err := Block(Input{Columns: maxTracks + 1, Boxes: boxes}, testParams)
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func TestLatticeBeyondItsCapOverflows(t *testing.T) {
	boxes := make([]Box, 700)
	for i := range boxes {
		boxes[i] = leaf(-1, maxTracks, 1, 1)
	}
	_, err := Block(Input{Columns: maxTracks, Boxes: boxes, Edges: []Edge{{From: 0, To: 1}}}, testParams)
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func TestDeepNestingIsRejected(t *testing.T) {
	boxes := make([]Box, maxDepth+3)
	for i := range boxes {
		boxes[i] = composite(i-1, 1, 1)
	}
	_, err := Block(Input{Boxes: boxes}, testParams)
	require.ErrorIs(t, err, geom.ErrDomain)
}

func TestEdgeCorridorWidensGaps(t *testing.T) {
	boxes := []Box{leaf(-1, 1, 20, 10), leaf(-1, 1, 20, 10)}
	plain := mustBlock(t, Input{Columns: 2, Boxes: boxes})
	routed := mustBlock(t, Input{Columns: 2, Boxes: boxes, Edges: []Edge{{From: 0, To: 1}}})
	require.Equal(t, plain.Rects[1].X-plain.Rects[0].X-plain.Rects[0].W, int32(8))
	require.Equal(t, routed.Rects[1].X-routed.Rects[0].X-routed.Rects[0].W, int32(16))
}

func TestLabelWidensTheGap(t *testing.T) {
	boxes := []Box{leaf(-1, 1, 20, 10), leaf(-1, 1, 20, 10)}
	out := mustBlock(t, Input{Columns: 2, Boxes: boxes, Edges: []Edge{{From: 0, To: 1, Label: geom.Size{W: 30, H: 12}}}})
	require.Equal(t, int32(16+30), out.Rects[1].X-out.Rects[0].X-out.Rects[0].W)
}

func assertRoute(t *testing.T, in Input, out Layout, k int) {
	t.Helper()
	e := in.Edges[k]
	route := out.Routes[k]
	require.GreaterOrEqual(t, len(route), 2)
	require.True(t, geom.IsOrthogonal(route))
	require.True(t, onBoundary(route[0], out.Rects[e.From]))
	require.True(t, onBoundary(route[len(route)-1], out.Rects[e.To]))
	for i, box := range in.Boxes {
		if box.Kind != KindLeaf || i == e.From || i == e.To {
			continue
		}
		hits, err := geom.PolylineHitsRect(route, out.Rects[i])
		require.NoError(t, err)
		require.False(t, hits, "route %d crosses leaf %d", k, i)
	}
}

func onBoundary(p geom.Point, r geom.Rect) bool {
	inside := p.X >= r.X && p.X <= r.X+r.W && p.Y >= r.Y && p.Y <= r.Y+r.H
	edge := p.X == r.X || p.X == r.X+r.W || p.Y == r.Y || p.Y == r.Y+r.H
	return inside && edge
}

func TestRoutesAvoidLeaves(t *testing.T) {
	in := Input{
		Columns: 3,
		Boxes:   []Box{leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10)},
		Edges:   []Edge{{From: 0, To: 2}, {From: 0, To: 5}, {From: 4, To: 1}, {From: 3, To: 3}},
	}
	out := mustBlock(t, in)
	for k := range in.Edges {
		assertRoute(t, in, out, k)
	}
}

func TestRoutesBetweenCompositeLeavesStayValid(t *testing.T) {
	in := Input{
		Columns: 2,
		Boxes:   []Box{composite(-1, 1, 2), leaf(0, 1, 30, 10), leaf(0, 1, 30, 10), composite(-1, 1, 1), leaf(3, 1, 30, 10)},
		Edges:   []Edge{{From: 1, To: 4}, {From: 4, To: 2}, {From: 0, To: 3}, {From: 4, To: 3}},
	}
	out := mustBlock(t, in)
	for k := range in.Edges {
		assertRoute(t, in, out, k)
	}
}

func TestSelfLoopLeavesAndEntersTheSameBox(t *testing.T) {
	in := Input{Columns: 1, Boxes: []Box{leaf(-1, 1, 30, 30)}, Edges: []Edge{{From: 0, To: 0}}}
	out := mustBlock(t, in)
	route := out.Routes[0]
	require.Len(t, route, 4)
	box := out.Rects[0]
	require.Equal(t, box.X+box.W, route[0].X)
	require.Equal(t, box.X+box.W, route[3].X)
	require.Greater(t, route[1].X, route[0].X)
	require.Less(t, route[0].Y, route[3].Y)
}

func TestParallelRoutesDoNotShareRuns(t *testing.T) {
	in := Input{
		Columns: 4,
		Boxes:   []Box{leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10)},
		Edges:   []Edge{{From: 0, To: 2}, {From: 1, To: 3}},
	}
	out := mustBlock(t, in)
	require.False(t, shareHorizontalRun(out.Routes[0], out.Routes[1]))
}

func shareHorizontalRun(a, b []geom.Point) bool {
	for i := 1; i < len(a); i++ {
		for j := 1; j < len(b); j++ {
			if a[i-1].Y != a[i].Y || b[j-1].Y != b[j].Y || a[i].Y != b[j].Y {
				continue
			}
			lo, hi := max(min(a[i-1].X, a[i].X), min(b[j-1].X, b[j].X)), min(max(a[i-1].X, a[i].X), max(b[j-1].X, b[j].X))
			if lo < hi {
				return true
			}
		}
	}
	return false
}

func labelledEdge(from, to int) Edge {
	return Edge{From: from, To: to, Label: geom.Size{W: 20, H: 8}}
}

func assertLabelClear(t *testing.T, in Input, out Layout, k int) {
	t.Helper()
	label := out.Labels[k]
	require.Equal(t, in.Edges[k].Label, geom.Size{W: label.W, H: label.H})
	assertLabelInsideFrames(t, in, out, label)
	for i := range in.Boxes {
		require.False(t, overlaps(label, out.Rects[i]), "label %d overlaps box %d", k, i)
	}
	for j := range k {
		require.False(t, overlaps(label, out.Labels[j]), "labels %d and %d overlap", k, j)
	}
	for _, route := range out.Routes {
		for i := 1; i < len(route); i++ {
			require.False(t, segmentTouches(route[i-1], route[i], testParams.LineThickness, label))
		}
	}
}

func TestLabelsAvoidBoxesRoutesAndEachOther(t *testing.T) {
	in := Input{
		Columns: 3,
		Boxes:   []Box{leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10)},
		Edges:   []Edge{labelledEdge(0, 1), labelledEdge(1, 2), labelledEdge(0, 3)},
	}
	out := mustBlock(t, in)
	for k := range in.Edges {
		assertLabelClear(t, in, out, k)
	}
}

func TestCrowdedLabelsSpillInsideTheCanvas(t *testing.T) {
	in := Input{Columns: 2, Boxes: []Box{leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10)}}
	for range 6 {
		in.Edges = append(in.Edges, labelledEdge(0, 1))
	}
	out := mustBlock(t, in)
	for k := range in.Edges {
		assertLabelClear(t, in, out, k)
	}
}

func TestLabelBesideASelfLoopStaysStrictlyInsideTheCellCanvas(t *testing.T) {
	in := Input{
		Boxes: []Box{leaf(-1, 1, 3, 3), leaf(-1, 1, 3, 3)},
		Edges: []Edge{{From: 0, To: 0}, {From: 1, To: 1, Label: geom.Size{W: 10, H: 1}}, {From: 0, To: 1}, {From: 1, To: 0}},
	}
	out, err := Block(in, Params{Padding: 1, BendCost: 4, LineThickness: 1})
	require.NoError(t, err)
	assertLabelInsideFrames(t, in, out, out.Labels[1])
}

func TestSpillMarginIsAtLeastOneUnitWithoutPadding(t *testing.T) {
	in := Input{Columns: 2, Boxes: []Box{leaf(-1, 1, 30, 10), leaf(-1, 1, 30, 10)}}
	for range 6 {
		in.Edges = append(in.Edges, labelledEdge(0, 1))
	}
	out, err := Block(in, Params{Padding: 0, BendCost: 64, LineThickness: 0})
	require.NoError(t, err)
	for k := range in.Edges {
		assertLabelInsideFrames(t, in, out, out.Labels[k])
	}
}

type xorshift uint32

func (x *xorshift) next(n int) int {
	*x ^= *x << 13
	*x ^= *x >> 17
	*x ^= *x << 5
	return int(uint32(*x) % uint32(n))
}

func randomInput(seed uint32) Input {
	rng := xorshift(seed*2654435761 + 1)
	for range 8 {
		rng.next(2)
	}
	in := Input{Columns: int32(rng.next(5))}
	composites := []int{-1}
	for n := 2 + rng.next(14); len(in.Boxes) < n; {
		parent := composites[rng.next(len(composites))]
		span := int32(1 + rng.next(3))
		switch rng.next(6) {
		case 0:
			in.Boxes = append(in.Boxes, space(parent))
		case 1:
			in.Boxes = append(in.Boxes, composite(parent, span, int32(rng.next(4))))
			composites = append(composites, len(in.Boxes)-1)
		default:
			in.Boxes = append(in.Boxes, leaf(parent, span, int32(5+rng.next(60)), int32(4+rng.next(20))))
		}
	}
	var linkable []int
	for i, b := range in.Boxes {
		if b.Kind != KindSpace {
			linkable = append(linkable, i)
		}
	}
	for range rng.next(8) {
		if len(linkable) == 0 {
			break
		}
		edge := Edge{From: linkable[rng.next(len(linkable))], To: linkable[rng.next(len(linkable))]}
		if rng.next(3) == 0 {
			edge.Label = geom.Size{W: int32(4 + rng.next(30)), H: int32(4 + rng.next(10))}
		}
		in.Edges = append(in.Edges, edge)
	}
	return in
}

func TestRandomLayoutsKeepTheirInvariants(t *testing.T) {
	for seed := range uint32(400) {
		in := randomInput(seed)
		out, err := Block(in, testParams)
		require.NoError(t, err, seed)
		again, err := Block(in, testParams)
		require.NoError(t, err, seed)
		require.Equal(t, out, again, seed)
		assertInvariants(t, seed, in, out)
	}
}

func assertInvariants(t *testing.T, seed uint32, in Input, out Layout) {
	t.Helper()
	canvas := geom.Rect{W: out.Canvas.W, H: out.Canvas.H}
	for i, box := range in.Boxes {
		ok, err := geom.Contains(canvas, out.Rects[i])
		require.NoError(t, err, seed)
		require.True(t, ok, "seed %d box %d outside canvas", seed, i)
		if box.Parent >= 0 {
			ok, err = geom.Contains(out.Rects[box.Parent], out.Rects[i])
			require.NoError(t, err, seed)
			require.True(t, ok, "seed %d box %d outside parent", seed, i)
		}
		for j := range i {
			if in.Boxes[j].Parent != box.Parent || box.Kind == KindSpace || in.Boxes[j].Kind == KindSpace {
				continue
			}
			hit, err := geom.Intersects(out.Rects[i], out.Rects[j])
			require.NoError(t, err, seed)
			require.False(t, hit, "seed %d siblings %d and %d overlap", seed, j, i)
		}
	}
	for k, edge := range in.Edges {
		assertRoute(t, in, out, k)
		if edge.Label != (geom.Size{}) {
			assertLabelInsideFrames(t, in, out, out.Labels[k])
		}
	}
}

func assertLabelInsideFrames(t *testing.T, in Input, out Layout, label geom.Rect) {
	t.Helper()
	canvas := geom.Rect{W: out.Canvas.W, H: out.Canvas.H}
	require.True(t, strictlyInside(canvas, label), "label %v touches the canvas edge", label)
	for i, box := range in.Boxes {
		if box.Kind != KindComposite {
			continue
		}
		frame := out.Rects[i]
		require.True(t, !overlaps(frame, label) || strictlyInside(frame, label), "label %v straddles frame %d", label, i)
	}
}
