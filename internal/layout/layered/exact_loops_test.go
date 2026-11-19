package layered

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func TestExactLoopPoints(t *testing.T) {
	site := loopSite{rect: geom.Rect{X: 10, Y: 20, W: 30, H: 14}, slot: 3, band: 6, index: 1, total: 2}
	points, err := site.exactPoints()
	require.NoError(t, err)
	require.Equal(t, []geom.Point{
		{X: 40, Y: 28}, {X: 49, Y: 28}, {X: 49, Y: 32}, {X: 52, Y: 32}, {X: 52, Y: 31}, {X: 40, Y: 31},
	}, points)
}

func TestExactLoopExtentAndNoHeightGrowth(t *testing.T) {
	g := &Graph{
		Params: Params{Slot: 4},
		Nodes:  []Node{{ID: "a", W: 10, H: 5, Exact: true}},
		Edges: []Edge{
			{Tail: 0, Head: 0, MinLen: 1, Label: &EdgeLabel{W: 7, H: 9}},
			{Tail: 0, Head: 0, MinLen: 1, Decl: 1},
		},
	}
	require.NoError(t, sizeLoops(g))
	require.Equal(t, int32(5), g.Nodes[0].H)
	require.Equal(t, int32(4*5+7), g.Nodes[0].Extent)
}

func TestReserveExactRanksShiftsFollowingRanks(t *testing.T) {
	g := &Graph{
		Params: Params{Slot: 1},
		Nodes:  []Node{{ID: "a", W: 2, H: 2, Exact: true, Role: scene.RoleNode}, {ID: "b", W: 2, H: 2}},
		Edges:  []Edge{{Tail: 0, Head: 0, MinLen: 1, Label: &EdgeLabel{W: 1, H: 8}}},
	}
	p := &Proper{Nodes: []ProperNode{{Node: g.Nodes[0]}, {Node: g.Nodes[1]}}, Rank: []int32{0, 1}}
	y := []int32{0, 10}
	top := []int32{0, 10}
	require.NoError(t, reserveExactRanks(g, p, [][]int32{{0}, {1}}, y, top))
	require.Equal(t, []int32{0, 16}, top)
	require.Equal(t, []int32{0, 16}, y)
}
