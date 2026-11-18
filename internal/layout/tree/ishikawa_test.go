package tree

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var cellFish = IshikawaParams{
	SpineBase: 40, RibMin: 12, RibPool: 80, MinSpacing: 4,
	BoneStub: 3, BoneBase: 6, BonePerChild: 1, Inset: 2, Cos: 4561, Sin: 32455,
}

var vectorFish = IshikawaParams{
	SpineBase: 16000, RibMin: 4800, RibPool: 32000, MinSpacing: 1792,
	BoneStub: 1920, BoneBase: 3840, BonePerChild: 320, Inset: 1280, Cos: 4561, Sin: 32455,
}

func box(x, y, w, h int32) geom.Rect { return geom.Rect{X: x, Y: y, W: w, H: h} }

func pts(xy ...int32) []geom.Point {
	out := make([]geom.Point, 0, len(xy)/2)
	for i := 0; i < len(xy); i += 2 {
		out = append(out, geom.Point{X: xy[i], Y: xy[i+1]})
	}
	return out
}

func TestIshikawaEffectOnly(t *testing.T) {
	got, err := Ishikawa([]Node{{Parent: NoParent, Width: 6, Height: 3}}, cellFish)
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{box(0, 39, 6, 3)}, got.Boxes)
	require.Equal(t, [][]geom.Point{nil}, got.Routes)
}

func TestIshikawaEmptyInput(t *testing.T) {
	got, err := Ishikawa(nil, cellFish)
	require.NoError(t, err)
	require.Empty(t, got.Boxes)
}

func TestIshikawaLeafCauseShiftsLeftByItsReach(t *testing.T) {
	nodes := []Node{{Parent: NoParent, Width: 6, Height: 3}, {Parent: 0, Width: 5, Height: 3}}
	got, err := Ishikawa(nodes, cellFish)
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{box(0, 39, 6, 3), box(-5, 29, 5, 3)}, got.Boxes)
	require.Equal(t, pts(-5, 40, 0, 40), got.Routes[0])
	require.Equal(t, pts(-2, 40, -3, 32), got.Routes[1])
}

func TestIshikawaBothSidesMirrorAroundTheSpine(t *testing.T) {
	nodes := []Node{{Parent: NoParent, Width: 6, Height: 3}, {Parent: 0, Width: 5, Height: 3}, {Parent: 0, Width: 5, Height: 3}}
	got, err := Ishikawa(nodes, cellFish)
	require.NoError(t, err)
	require.Equal(t, box(-5, 29, 5, 3), got.Boxes[1])
	require.Equal(t, box(-5, 48, 5, 3), got.Boxes[2])
	require.Equal(t, pts(-2, 40, -3, 48), got.Routes[2])
}

func TestIshikawaSubCausesFollowTheUpstreamSlots(t *testing.T) {
	nodes := []Node{
		{Parent: NoParent, Width: 6, Height: 3},
		{Parent: 0, Width: 5, Height: 3},
		{Parent: 1, Width: 3, Height: 1},
		{Parent: 1, Width: 3, Height: 1},
	}
	got, err := Ishikawa(nodes, cellFish)
	require.NoError(t, err)
	require.Equal(t, box(0, 79, 6, 3), got.Boxes[0])
	require.Equal(t, box(-15, -3, 5, 3), got.Boxes[1])
	require.Equal(t, box(-12, 54, 3, 1), got.Boxes[3])
	require.Equal(t, box(-16, 27, 3, 1), got.Boxes[2])
	require.Equal(t, pts(-2, 80, -13, 0), got.Routes[1])
	require.Equal(t, pts(-6, 54, -9, 54), got.Routes[3])
	require.Equal(t, pts(-10, 27, -13, 27), got.Routes[2])
	require.Equal(t, pts(-16, 80, 0, 80), got.Routes[0])
}

func TestIshikawaLowerSideKeepsDeclarationOrder(t *testing.T) {
	nodes := []Node{
		{Parent: NoParent, Width: 6, Height: 3},
		{Parent: 0, Width: 5, Height: 3},
		{Parent: 0, Width: 5, Height: 3},
		{Parent: 2, Width: 3, Height: 1},
		{Parent: 2, Width: 3, Height: 1},
	}
	got, err := Ishikawa(nodes, cellFish)
	require.NoError(t, err)
	first, second := got.Routes[3][1].Y, got.Routes[4][1].Y
	require.Less(t, first, second)
	require.Greater(t, first, got.Routes[0][0].Y)
}

func TestIshikawaDiagonalBonesShareTheRibSlope(t *testing.T) {
	nodes := []Node{
		{Parent: NoParent, Width: 6, Height: 3},
		{Parent: 0, Width: 5, Height: 3},
		{Parent: 1, Width: 3, Height: 1},
		{Parent: 2, Width: 3, Height: 1},
		{Parent: 3, Width: 3, Height: 1},
		{Parent: 2, Width: 3, Height: 1},
	}
	for _, params := range []IshikawaParams{cellFish, vectorFish} {
		got, err := Ishikawa(nodes, params)
		require.NoError(t, err)
		for i := 1; i < len(nodes); i++ {
			route := got.Routes[i]
			dx, dy := int64(route[1].X)-int64(route[0].X), int64(route[1].Y)-int64(route[0].Y)
			if dy == 0 {
				require.Equal(t, 0, depthOf(nodes, i)%2, "horizontal bone of node %d", i)
				continue
			}
			require.Equal(t, 1, depthOf(nodes, i)%2, "node %d", i)
			require.Equal(t, -geom.FloorDiv(max(dy, -dy)*int64(params.Cos), int64(params.Sin)), dx, "node %d", i)
		}
	}
}

func depthOf(nodes []Node, i int) int {
	d := 0
	for nodes[i].Parent != NoParent {
		i, d = nodes[i].Parent, d+1
	}
	return d
}

func TestIshikawaRejectsBadInput(t *testing.T) {
	root := Node{Parent: NoParent, Width: 1, Height: 1}
	for name, nodes := range map[string][]Node{
		"rooted":     {{Parent: 0, Width: 1, Height: 1}},
		"empty box":  {root, {Parent: 0, Width: 0, Height: 1}},
		"orphan":     {root, {Parent: 5, Width: 1, Height: 1}},
		"off branch": {root, {Parent: 0, Width: 1, Height: 1}, {Parent: 1, Width: 1, Height: 1}, {Parent: 1, Width: 1, Height: 1}, {Parent: 2, Width: 1, Height: 1}},
	} {
		_, err := Ishikawa(nodes, cellFish)
		require.ErrorIs(t, err, ErrInvalid, name)
	}
	bad := cellFish
	bad.Sin = 0
	_, err := Ishikawa([]Node{root}, bad)
	require.ErrorIs(t, err, ErrInvalid)
}

func TestIshikawaRejectsTooDeepTrees(t *testing.T) {
	nodes := []Node{{Parent: NoParent, Width: 1, Height: 1}}
	for i := 1; i <= IshikawaMaxDepth+1; i++ {
		nodes = append(nodes, Node{Parent: i - 1, Width: 1, Height: 1})
	}
	_, err := Ishikawa(nodes[:IshikawaMaxDepth+1], cellFish)
	require.NoError(t, err)
	_, err = Ishikawa(nodes, cellFish)
	require.ErrorIs(t, err, ErrInvalid)
}
