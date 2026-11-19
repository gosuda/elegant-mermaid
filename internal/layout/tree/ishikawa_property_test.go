package tree

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type fishDraw struct{ state uint32 }

func (d *fishDraw) next(n int) int {
	d.state ^= d.state << 13
	d.state ^= d.state >> 17
	d.state ^= d.state << 5
	return int(d.state % uint32(n))
}

func randomFish(seed uint32, maxNodes int, maxW, maxH int) []Node {
	d := &fishDraw{state: seed}
	count := 1 + d.next(maxNodes)
	nodes := []Node{{Parent: NoParent, Width: int32(1 + d.next(maxW)), Height: int32(1 + d.next(maxH))}}
	path := []int{0}
	for i := 1; i < count; i++ {
		keep := 1 + d.next(len(path))
		path = path[:keep]
		nodes = append(nodes, Node{Parent: path[keep-1], Width: int32(1 + d.next(maxW)), Height: int32(1 + d.next(maxH))})
		path = append(path, i)
	}
	return nodes
}

func onBoundary(p geom.Point, r geom.Rect) bool {
	inside := p.X >= r.X && p.X <= r.X+r.W && p.Y >= r.Y && p.Y <= r.Y+r.H
	return inside && (p.X == r.X || p.X == r.X+r.W || p.Y == r.Y || p.Y == r.Y+r.H)
}

func checkFish(t *testing.T, nodes []Node, params IshikawaParams, margin int32) {
	t.Helper()
	got, err := Ishikawa(nodes, params)
	require.NoError(t, err)
	canvas, err := Normalize(&got, margin)
	require.NoError(t, err)
	for i, a := range got.Boxes {
		require.GreaterOrEqual(t, a.X, int32(0))
		require.GreaterOrEqual(t, a.Y, int32(0))
		require.LessOrEqual(t, a.X+a.W, canvas.W)
		require.LessOrEqual(t, a.Y+a.H, canvas.H)
		for j := i + 1; j < len(got.Boxes); j++ {
			hit, err := geom.Intersects(a, got.Boxes[j])
			require.NoError(t, err)
			require.False(t, hit, "boxes %d and %d overlap: %v %v", i, j, a, got.Boxes[j])
		}
	}
	for k, route := range got.Routes {
		if route == nil {
			continue
		}
		require.True(t, onBoundary(route[len(route)-1], got.Boxes[k]), "route %d ends off its box", k)
		for j, b := range got.Boxes {
			if j == k {
				continue
			}
			hit, err := geom.PolylineHitsRect(route, b)
			require.NoError(t, err)
			require.False(t, hit, "route %d crosses box %d: %v %v", k, j, route, b)
		}
		if k == 0 || depthOf(nodes, k)%2 == 0 {
			require.True(t, geom.IsOrthogonal(route), "route %d is not orthogonal", k)
		}
	}
}

func TestIshikawaRandomTreesStayClear(t *testing.T) {
	profiles := []struct {
		name         string
		params       IshikawaParams
		margin       int32
		maxW, maxH   int
		maxNodeCount int
	}{
		{"cell", cellFish, 1, 30, 6, 40},
		{"cell tall", cellFish, 1, 8, 25, 40},
		{"vector", vectorFish, 1024, 20000, 8000, 40},
		{"vector tall", vectorFish, 1024, 6000, 40000, 40},
	}
	for _, p := range profiles {
		for seed := uint32(1); seed <= 400; seed++ {
			t.Run(fmt.Sprintf("%s/%d", p.name, seed), func(t *testing.T) {
				checkFish(t, randomFish(seed, p.maxNodeCount, p.maxW, p.maxH), p.params, p.margin)
			})
		}
	}
}

func TestIshikawaWideBushesStayClear(t *testing.T) {
	for _, children := range []int{1, 2, 7, 30} {
		for _, params := range []IshikawaParams{cellFish, vectorFish} {
			nodes := []Node{{Parent: NoParent, Width: 6, Height: 3}, {Parent: 0, Width: 5, Height: 3}, {Parent: 1, Width: 4, Height: 3}}
			for k := 0; k < children; k++ {
				nodes = append(nodes, Node{Parent: 2, Width: 4, Height: 7})
			}
			nodes = append(nodes, Node{Parent: 0, Width: 5, Height: 3})
			checkFish(t, nodes, params, 1)
		}
	}
}
