package tree

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type stream uint32

func (s *stream) draw(lo, hi int) int {
	x := uint32(*s)
	x ^= x << 13
	x ^= x >> 17
	x ^= x << 5
	*s = stream(x)
	return lo + int(x%uint32(hi-lo+1))
}

func randomTree(seed int) []Node {
	s := stream(seed + 1)
	n := s.draw(2, 30)
	parents := make([]int, n)
	for i := 1; i < n; i++ {
		parents[i] = s.draw(0, i-1)
	}
	sizes := make([]Node, n)
	for i := range sizes {
		sizes[i] = Node{Width: int32(s.draw(20, 140)), Height: int32(s.draw(20, 60))}
	}
	children := make([][]int, n)
	for i := 1; i < n; i++ {
		children[parents[i]] = append(children[parents[i]], i)
	}
	order := make([]int, 0, n)
	var visit func(int)
	visit = func(v int) {
		order = append(order, v)
		for _, c := range children[v] {
			visit(c)
		}
	}
	visit(0)
	newIndex := make([]int, n)
	for at, old := range order {
		newIndex[old] = at
	}
	nodes := make([]Node, n)
	for at, old := range order {
		nodes[at] = Node{Parent: NoParent, Width: sizes[old].Width, Height: sizes[old].Height}
		if old != 0 {
			nodes[at].Parent = newIndex[parents[old]]
		}
	}
	return nodes
}

type oracle struct {
	nodes    []Node
	layout   Layout
	gaps     Gaps
	children [][]int
	right    []bool
}

func newOracle(nodes []Node, layout Layout, gaps Gaps) *oracle {
	o := &oracle{nodes: nodes, layout: layout, gaps: gaps, children: make([][]int, len(nodes)), right: make([]bool, len(nodes))}
	ordinal := 0
	for i := 1; i < len(nodes); i++ {
		parent := nodes[i].Parent
		o.children[parent] = append(o.children[parent], i)
		o.right[i] = o.right[parent]
		if parent == 0 {
			o.right[i] = ordinal%2 == 0
			ordinal++
		}
	}
	return o
}

func (o *oracle) refY(i int) int64 {
	b := o.layout.Boxes[i]
	return int64(b.Y) + geom.FloorDiv(int64(b.H), 2)
}

func (o *oracle) within(j, root int) bool {
	for ; j != NoParent; j = o.nodes[j].Parent {
		if j == root {
			return true
		}
	}
	return false
}

func (o *oracle) span(i int) (int64, int64) {
	b := o.layout.Boxes[i]
	if o.right[i] {
		return int64(b.X) - int64(o.gaps.Level), int64(b.X) + int64(b.W)
	}
	return int64(b.X), int64(b.X) + int64(b.W) + int64(o.gaps.Level)
}

func (o *oracle) lists(v int) [][]int {
	if v != 0 {
		return [][]int{o.children[v]}
	}
	var right, left []int
	for _, c := range o.children[0] {
		if o.right[c] {
			right = append(right, c)
		} else {
			left = append(left, c)
		}
	}
	return [][]int{right, left}
}

func (o *oracle) checkSeparation(t *testing.T, list []int, seed int) {
	t.Helper()
	for j := 1; j < len(list); j++ {
		tight := false
		for a := range o.nodes {
			if !o.earlier(a, list[:j]) {
				continue
			}
			for b := range o.nodes {
				if o.within(b, list[j]) {
					tight = o.checkPair(t, a, b, seed) || tight
				}
			}
		}
		require.True(t, tight, "seed %d sibling %d has slack", seed, list[j])
	}
}

func (o *oracle) checkPair(t *testing.T, a, b, seed int) bool {
	t.Helper()
	au0, au1 := o.span(a)
	bu0, bu1 := o.span(b)
	if au0 >= bu1 || bu0 >= au1 {
		return false
	}
	gap := int64(o.layout.Boxes[b].Y) - int64(o.layout.Boxes[a].Y) - int64(o.layout.Boxes[a].H)
	require.GreaterOrEqual(t, gap, int64(o.gaps.Sibling), "seed %d boxes %d and %d", seed, a, b)
	return gap == int64(o.gaps.Sibling)
}

func (o *oracle) earlier(a int, siblings []int) bool {
	for _, s := range siblings {
		if o.within(a, s) {
			return true
		}
	}
	return false
}

func (o *oracle) checkCentre(t *testing.T, v int, list []int, seed int) {
	t.Helper()
	if len(list) == 0 || v == 0 {
		return
	}
	first, last := o.refY(list[0]), o.refY(list[len(list)-1])
	require.Equal(t, geom.FloorDiv(first+last, 2), o.refY(v), "seed %d parent %d", seed, v)
}

func (o *oracle) checkPlacement(t *testing.T, seed int) {
	t.Helper()
	for i := 1; i < len(o.nodes); i++ {
		parent, box, pbox := o.nodes[i].Parent, o.layout.Boxes[i], o.layout.Boxes[o.nodes[i].Parent]
		if o.right[i] {
			require.Equal(t, int64(pbox.X)+int64(pbox.W)+int64(o.gaps.Level), int64(box.X), "seed %d node %d", seed, i)
			continue
		}
		require.Equal(t, int64(pbox.X)-int64(o.gaps.Level), int64(box.X)+int64(box.W), "seed %d node %d", seed, i)
		_ = parent
	}
}

func TestRandomTreesSatisfyTheContourRuleAndStayClear(t *testing.T) {
	for _, gaps := range []Gaps{{Level: 40, Sibling: 10}, {Level: 4, Sibling: 1}, {Level: 2, Sibling: 3}} {
		for seed := range 400 {
			nodes := randomTree(seed)
			l, err := Mindmap(nodes, gaps)
			require.NoError(t, err)
			o := newOracle(nodes, l, gaps)
			o.checkPlacement(t, seed)
			for v := range nodes {
				for _, list := range o.lists(v) {
					o.checkSeparation(t, list, seed)
					o.checkCentre(t, v, list, seed)
				}
			}
			requireClear(t, nodes, l)
			for i := 1; i < len(nodes); i++ {
				require.True(t, geom.IsOrthogonal(l.Routes[i]), "seed %d route %d", seed, i)
			}
		}
	}
}

func TestRouteEndsSitOnTheNearAndFarEdgesAtTheReferenceLine(t *testing.T) {
	for seed := range 100 {
		nodes := randomTree(seed)
		l, err := Mindmap(nodes, testGaps)
		require.NoError(t, err)
		o := newOracle(nodes, l, testGaps)
		for i := 1; i < len(nodes); i++ {
			parent, child := l.Boxes[nodes[i].Parent], l.Boxes[i]
			route := l.Routes[i]
			start, end := route[0], route[len(route)-1]
			require.Equal(t, int32(o.refY(nodes[i].Parent)), start.Y)
			require.Equal(t, int32(o.refY(i)), end.Y)
			if o.right[i] {
				require.Equal(t, parent.X+parent.W, start.X)
				require.Equal(t, child.X, end.X)
			} else {
				require.Equal(t, parent.X, start.X)
				require.Equal(t, child.X+child.W, end.X)
			}
		}
	}
}
