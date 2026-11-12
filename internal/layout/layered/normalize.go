package layered

import (
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type ProperNode struct {
	Node
	Dummy bool
	Edge  int32
}
type ProperEdge struct{ Tail, Head, Decl, Original int32 }
type Proper struct {
	Nodes   []ProperNode
	Edges   []ProperEdge
	Rank    []int32
	Chains  [][]int32
	Out, In [][]int32
	Params
}

func Normalize(g *Graph, rank []int32) (*Proper, error) {
	if err := validateGraph(g); err != nil {
		return nil, err
	}
	if len(rank) != len(g.Nodes) {
		return nil, ErrRanking
	}
	slot, err := normalizationSlot(g)
	if err != nil {
		return nil, err
	}
	p := &Proper{Rank: slices.Clone(rank), Chains: make([][]int32, len(g.Edges)), Params: g.Params}
	for _, n := range g.Nodes {
		p.Nodes = append(p.Nodes, ProperNode{Node: n, Edge: -1})
	}
	for i, e := range g.Edges {
		if e.SelfLoop() {
			continue
		}
		if err := normalizeEdge(p, e, int32(i), slot); err != nil {
			return nil, err
		}
	}
	p.Out = make([][]int32, len(p.Nodes))
	p.In = make([][]int32, len(p.Nodes))
	for i, e := range p.Edges {
		p.Out[e.Tail] = append(p.Out[e.Tail], int32(i))
		p.In[e.Head] = append(p.In[e.Head], int32(i))
	}
	return p, nil
}

func normalizationSlot(g *Graph) (int32, error) {
	if g.Slot < 0 {
		return 0, ErrGraph
	}
	if g.Slot > 0 {
		return g.Slot, nil
	}
	p, err := DefaultParams(scene.ProfileVector)
	return p.Slot, err
}

func normalizeEdge(p *Proper, e Edge, index, slot int32) error {
	a, b := e.Chain()
	span := int64(p.Rank[b]) - int64(p.Rank[a])
	if span < int64(e.MinLen) {
		return ErrRanking
	}
	if int64(len(p.Nodes))+span-1 > math.MaxInt32 || int64(len(p.Edges))+span > math.MaxInt32 {
		return geom.ErrOverflow
	}
	chain := make([]int32, 0, span+1)
	chain = append(chain, a)
	for k := int64(1); k < span; k++ {
		v := int32(len(p.Nodes))
		r := int32(int64(p.Rank[a]) + k)
		p.Nodes = append(p.Nodes, ProperNode{Node: Node{Decl: e.Decl, W: slot}, Dummy: true, Edge: index})
		p.Rank = append(p.Rank, r)
		chain = append(chain, v)
	}
	chain = append(chain, b)
	p.Chains[index] = chain
	for k := 1; k < len(chain); k++ {
		p.Edges = append(p.Edges, ProperEdge{Tail: chain[k-1], Head: chain[k], Decl: e.Decl, Original: index})
	}
	return nil
}
