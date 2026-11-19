package tree

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var testGaps = Gaps{Level: 40, Sibling: 10}

func leaf(parent int, w, h int32) Node { return Node{Parent: parent, Width: w, Height: h} }

func TestSingleNodeSitsCentredOnTheOrigin(t *testing.T) {
	l, err := Mindmap([]Node{leaf(NoParent, 11, 7)}, testGaps)
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{{X: -5, Y: -3, W: 11, H: 7}}, l.Boxes)
}

func TestRootChildrenAlternateSides(t *testing.T) {
	l, err := Mindmap([]Node{leaf(NoParent, 10, 6), leaf(0, 8, 4), leaf(0, 6, 4)}, Gaps{Level: 4, Sibling: 2})
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{{X: -5, Y: -3, W: 10, H: 6}, {X: 9, Y: -2, W: 8, H: 4}, {X: -15, Y: -2, W: 6, H: 4}}, l.Boxes)
	require.Equal(t, []geom.Point{{X: 5, Y: 0}, {X: 9, Y: 0}}, l.Routes[1])
	require.Equal(t, []geom.Point{{X: -5, Y: 0}, {X: -9, Y: 0}}, l.Routes[2])
}

func TestSiblingsStackBelowTheContourAndCentreOnTheParent(t *testing.T) {
	nodes := []Node{leaf(NoParent, 10, 6), leaf(0, 8, 4), leaf(0, 6, 4), leaf(0, 8, 4)}
	l, err := Mindmap(nodes, Gaps{Level: 4, Sibling: 2})
	require.NoError(t, err)
	require.Equal(t, geom.Rect{X: 9, Y: -5, W: 8, H: 4}, l.Boxes[1])
	require.Equal(t, geom.Rect{X: 9, Y: 1, W: 8, H: 4}, l.Boxes[3])
	require.Equal(t, []geom.Point{{X: 5, Y: 0}, {X: 7, Y: 0}, {X: 7, Y: -3}, {X: 9, Y: -3}}, l.Routes[1])
	require.Equal(t, []geom.Point{{X: 5, Y: 0}, {X: 7, Y: 0}, {X: 7, Y: 3}, {X: 9, Y: 3}}, l.Routes[3])
}

func TestDeeperBoxBindsTheSiblingOffset(t *testing.T) {
	nodes := []Node{leaf(NoParent, 10, 6), leaf(0, 4, 2), leaf(1, 20, 20), leaf(0, 4, 2), leaf(0, 10, 2)}
	gaps := Gaps{Level: 3, Sibling: 2}
	wide, err := Mindmap(nodes, gaps)
	require.NoError(t, err)
	require.Equal(t, int32(13), wide.Boxes[4].Y-wide.Boxes[1].Y)
	nodes[4].Width = 4
	narrow, err := Mindmap(nodes, gaps)
	require.NoError(t, err)
	require.Equal(t, int32(4), narrow.Boxes[4].Y-narrow.Boxes[1].Y)
}

func TestOddParentCentreRoundsDown(t *testing.T) {
	nodes := []Node{leaf(NoParent, 10, 6), leaf(0, 10, 3), leaf(1, 10, 3), leaf(1, 10, 3)}
	l, err := Mindmap(nodes, Gaps{Level: 4, Sibling: 1})
	require.NoError(t, err)
	child := func(i int) int32 { return l.Boxes[i].Y + l.Boxes[i].H/2 }
	require.Equal(t, int32(4), child(3)-child(2))
	require.Equal(t, geom.FloorDiv(int64(child(2)+child(3)), 2), int64(child(1)))
}

func TestInvalidInputIsRejected(t *testing.T) {
	for name, nodes := range map[string][]Node{
		"root has parent":   {leaf(0, 4, 4)},
		"forward parent":    {leaf(NoParent, 4, 4), leaf(2, 4, 4), leaf(0, 4, 4)},
		"zero width":        {leaf(NoParent, 0, 4)},
		"zero height":       {leaf(NoParent, 4, 0)},
		"second root":       {leaf(NoParent, 4, 4), leaf(NoParent, 4, 4)},
		"not preorder":      {leaf(NoParent, 4, 4), leaf(0, 4, 4), leaf(0, 4, 4), leaf(1, 4, 4)},
		"negative parent":   {leaf(NoParent, 4, 4), leaf(-2, 4, 4)},
		"parent is itself":  {leaf(NoParent, 4, 4), leaf(1, 4, 4)},
		"parent out of set": {leaf(NoParent, 4, 4), leaf(7, 4, 4)},
	} {
		_, err := Mindmap(nodes, testGaps)
		require.ErrorIs(t, err, ErrInvalid, name)
	}
	_, err := Mindmap([]Node{leaf(NoParent, 4, 4)}, Gaps{Level: 4})
	require.ErrorIs(t, err, ErrInvalid)
}

func TestEmptyInputHasNoBoxes(t *testing.T) {
	l, err := Mindmap(nil, testGaps)
	require.NoError(t, err)
	require.Empty(t, l.Boxes)
	size, err := Normalize(&l, 8)
	require.NoError(t, err)
	require.Equal(t, geom.Size{W: 16, H: 16}, size)
}

func TestHugeNodesOverflow(t *testing.T) {
	huge := int32(geom.CoordLimit)
	_, err := Mindmap([]Node{leaf(NoParent, huge, 4), leaf(0, huge, 4)}, testGaps)
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func TestNormalizeShiftsBoxesAndRoutesByTheMargin(t *testing.T) {
	l, err := Mindmap([]Node{leaf(NoParent, 10, 6), leaf(0, 8, 4), leaf(1, 6, 8), leaf(0, 6, 4)}, Gaps{Level: 4, Sibling: 2})
	require.NoError(t, err)
	before := l.Boxes[0]
	size, err := Normalize(&l, 3)
	require.NoError(t, err)
	minX, minY, maxX, maxY := int32(1<<30), int32(1<<30), int32(-1<<30), int32(-1<<30)
	for _, b := range l.Boxes {
		minX, minY = min(minX, b.X), min(minY, b.Y)
		maxX, maxY = max(maxX, b.X+b.W), max(maxY, b.Y+b.H)
	}
	require.Equal(t, int32(3), minX)
	require.Equal(t, int32(3), minY)
	require.Equal(t, geom.Size{W: maxX + 3, H: maxY + 3}, size)
	require.Equal(t, before.W, l.Boxes[0].W)
	require.Equal(t, l.Boxes[0].X+l.Boxes[0].W, l.Routes[1][0].X)
}

func crossingTree() []Node {
	return []Node{leaf(NoParent, 20, 20), leaf(0, 80, 20), leaf(0, 20, 20), leaf(0, 50, 20), leaf(3, 20, 30), leaf(3, 20, 30), leaf(3, 20, 30)}
}

func TestWidenedContourKeepsRoutesOffForeignBoxes(t *testing.T) {
	literalE := geom.Rect{X: 50, Y: -25, W: 80, H: 20}
	literalRoute := []geom.Point{{X: 100, Y: 15}, {X: 120, Y: 15}, {X: 120, Y: -25}, {X: 140, Y: -25}}
	hit, err := geom.PolylineHitsRect(literalRoute, literalE)
	require.NoError(t, err)
	require.True(t, hit, "the box-only contour places the first child beside the wide sibling, so the trunk crosses it")

	nodes := crossingTree()
	l, err := Mindmap(nodes, testGaps)
	require.NoError(t, err)
	requireClear(t, nodes, l)
	require.GreaterOrEqual(t, l.Boxes[4].Y, l.Boxes[1].Y+l.Boxes[1].H+testGaps.Sibling)
}

func requireClear(t *testing.T, nodes []Node, l Layout) {
	t.Helper()
	for i, a := range l.Boxes {
		for j := i + 1; j < len(l.Boxes); j++ {
			overlap, err := geom.Intersects(a, l.Boxes[j])
			require.NoError(t, err)
			require.False(t, overlap, "boxes %d and %d overlap", i, j)
		}
	}
	for i := 1; i < len(l.Routes); i++ {
		for j, box := range l.Boxes {
			hit, err := geom.PolylineHitsRect(l.Routes[i], box)
			require.NoError(t, err)
			require.True(t, j == i || j == nodes[i].Parent || !hit, "route %d crosses box %d", i, j)
		}
	}
}
