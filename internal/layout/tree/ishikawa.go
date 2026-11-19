package tree

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

const (
	IshikawaMaxDepth = 64
	leafRibDivisor   = 5
	minRibLength     = leafRibDivisor
	marginSlack      = 3
)

type IshikawaParams struct {
	SpineBase, RibMin, RibPool, MinSpacing int32
	BoneStub, BoneBase, BonePerChild       int32
	Inset                                  int32
	Cos, Sin                               int32
}

type spot struct{ x, y int64 }

type relBox struct{ x, y, w, h int64 }

type piece struct {
	node  int
	box   relBox
	route [2]spot
}

type entry struct {
	node, parent, depth int
}

type rib struct {
	cause       int
	upper       bool
	entries     []entry
	order       []int
	heights     int64
	descendants int64
	length      int64
	pieces      []piece
}

type fish struct {
	nodes    []Node
	p        IshikawaParams
	children [][]int
	ribs     []rib
	spineY   int64
}

func Ishikawa(nodes []Node, p IshikawaParams) (Layout, error) {
	if len(nodes) == 0 {
		return Layout{}, nil
	}
	f, err := newFish(nodes, p)
	if err != nil {
		return Layout{}, err
	}
	f.sizeRibs()
	for i := range f.ribs {
		if err := f.place(&f.ribs[i]); err != nil {
			return Layout{}, err
		}
	}
	return f.assemble()
}

func (p IshikawaParams) valid() bool {
	return p.SpineBase >= minRibLength && p.RibMin >= minRibLength && p.RibPool >= 1 && p.MinSpacing >= 1 &&
		p.BoneStub >= 1 && p.BoneBase >= 1 && p.BonePerChild >= 0 && p.Inset >= 0 && p.Cos >= 0 && p.Sin >= 1
}

func newFish(nodes []Node, p IshikawaParams) (*fish, error) {
	if !p.valid() {
		return nil, ErrInvalid
	}
	children, depth, err := childLists(nodes)
	if err != nil {
		return nil, err
	}
	f := &fish{nodes: nodes, p: p, children: children}
	for k, cause := range children[0] {
		f.ribs = append(f.ribs, f.newRib(cause, k%2 == 0, depth))
	}
	return f, nil
}

func childLists(nodes []Node) ([][]int, []int, error) {
	children := make([][]int, len(nodes))
	depth := make([]int, len(nodes))
	var path []int
	for i, n := range nodes {
		if n.Width < 1 || n.Height < 1 {
			return nil, nil, ErrInvalid
		}
		if i == 0 {
			if n.Parent != NoParent {
				return nil, nil, ErrInvalid
			}
			path = append(path, 0)
			continue
		}
		path = unwind(path, n.Parent)
		if len(path) == 0 {
			return nil, nil, ErrInvalid
		}
		depth[i] = depth[n.Parent] + 1
		if depth[i] > IshikawaMaxDepth {
			return nil, nil, ErrInvalid
		}
		path = append(path, i)
		children[n.Parent] = append(children[n.Parent], i)
	}
	return children, depth, nil
}

func (f *fish) newRib(cause int, upper bool, depth []int) rib {
	r := rib{cause: cause, upper: upper}
	f.flatten(&r, f.children[cause], -1, depth)
	r.descendants = int64(len(r.entries))
	for _, e := range r.entries {
		r.heights = max(r.heights, int64(f.nodes[e.node].Height))
	}
	return r
}

func (f *fish) flatten(r *rib, list []int, parent int, depth []int) {
	for i := range list {
		child := list[i]
		if r.upper {
			child = list[len(list)-1-i]
		}
		idx := len(r.entries)
		r.entries = append(r.entries, entry{node: child, parent: parent, depth: depth[child]})
		if depth[child]%2 == 0 {
			r.order = append(r.order, idx)
		}
		f.flatten(r, f.children[child], idx, depth)
		if depth[child]%2 != 0 {
			r.order = append(r.order, idx)
		}
	}
}

func (r *rib) need(spacing int64) int64 {
	n := int64(len(r.entries))
	if n == 0 {
		return 0
	}
	return max(n*spacing, (n+1)*r.heights)
}

func (r *rib) side() int {
	if r.upper {
		return 0
	}
	return 1
}

func (f *fish) sideLengths() [2]int64 {
	var totals [2]int64
	for i := range f.ribs {
		totals[f.ribs[i].side()] += f.ribs[i].descendants
	}
	lengths := [2]int64{int64(f.p.SpineBase), int64(f.p.SpineBase)}
	if all := totals[0] + totals[1]; all > 0 {
		for s := range lengths {
			lengths[s] = max(int64(f.p.RibMin), geom.FloorDiv(int64(f.p.RibPool)*totals[s], all))
		}
	}
	for i := range f.ribs {
		s := f.ribs[i].side()
		lengths[s] = max(lengths[s], f.ribs[i].need(int64(f.p.MinSpacing)))
	}
	return lengths
}

func (f *fish) sizeRibs() {
	lengths := f.sideLengths()
	f.spineY = max(lengths[0], int64(f.p.SpineBase))
	for i := range f.ribs {
		r := &f.ribs[i]
		r.length = lengths[r.side()]
		if len(f.children[r.cause]) == 0 {
			r.length = geom.FloorDiv(r.length, leafRibDivisor)
		}
	}
}
