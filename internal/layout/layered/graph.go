package layered

import (
	"errors"
	"fmt"
	"math"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var (
	ErrGraph   = errors.New("layered: malformed graph")
	ErrCycle   = errors.New("layered: cyclic forward edges")
	ErrRanking = errors.New("layered: infeasible ranking")
)

type Node struct {
	ID   string
	Decl int32
	W    int32
	H    int32
}

type Edge struct {
	Tail     int32
	Head     int32
	MinLen   int32
	Decl     int32
	Reversed bool
}

func (e Edge) SelfLoop() bool {
	return e.Tail == e.Head
}

func (e Edge) Chain() (tail, head int32) {
	if e.Reversed {
		return e.Head, e.Tail
	}
	return e.Tail, e.Head
}

type Params struct {
	Slot        int32
	PivotFactor int32
	NodeGap     int32
	RankGap     int32
	PortGap     int32
}

type Graph struct {
	Nodes   []Node
	Edges   []Edge
	Out, In [][]int32
	Params
}

func DefaultParams(profile scene.Profile) (Params, error) {
	slotName := profile.String() + ".slot"
	pivotName := profile.String() + ".pivot_factor"
	var p Params
	var haveSlot, havePivot bool
	for _, c := range gen.LayoutConst {
		switch c.Name {
		case slotName:
			p.Slot, haveSlot = c.Value, true
		case pivotName:
			p.PivotFactor, havePivot = c.Value, true
		case profile.String() + ".node_gap":
			p.NodeGap = c.Value
		case profile.String() + ".rank_gap":
			p.RankGap = c.Value
		case profile.String() + ".port_gap":
			p.PortGap = c.Value
		}
	}
	if !haveSlot || !havePivot {
		return Params{}, fmt.Errorf("layered: constants of profile %q are missing: %w", profile, ErrGraph)
	}
	return p, nil
}

func validateGraph(g *Graph) error {
	if g == nil {
		return fmt.Errorf("layered: nil graph: %w", ErrGraph)
	}
	if int64(len(g.Nodes)) > math.MaxInt32 || int64(len(g.Edges)) > math.MaxInt32 {
		return fmt.Errorf("layered: more than %d nodes or edges: %w", math.MaxInt32, ErrGraph)
	}
	if err := validateNodes(g.Nodes); err != nil {
		return err
	}
	for i := range g.Edges {
		if err := validateEdge(g, i); err != nil {
			return err
		}
	}
	return nil
}

func validateEdge(g *Graph, i int) error {
	e := &g.Edges[i]
	n := int64(len(g.Nodes))
	if int64(e.Tail) < 0 || int64(e.Tail) >= n || int64(e.Head) < 0 || int64(e.Head) >= n {
		return fmt.Errorf("layered: edge %d joins %d and %d of %d nodes: %w", i, e.Tail, e.Head, n, ErrGraph)
	}
	if e.MinLen < 1 {
		return fmt.Errorf("layered: edge %d has minimum length %d: %w", i, e.MinLen, ErrGraph)
	}
	if i > 0 && e.Decl < g.Edges[i-1].Decl {
		return fmt.Errorf("layered: edge %d declares index %d after %d: %w", i, e.Decl, g.Edges[i-1].Decl, ErrGraph)
	}
	return nil
}

func declaredOut(g *Graph) [][]int32 {
	out := make([][]int32, len(g.Nodes))
	for i := range g.Edges {
		out[g.Edges[i].Tail] = append(out[g.Edges[i].Tail], int32(i))
	}
	return out
}

func incidentEdges(g *Graph) [][]int32 {
	out := make([][]int32, len(g.Nodes))
	for i := range g.Edges {
		e := &g.Edges[i]
		out[e.Tail] = append(out[e.Tail], int32(i))
		if !e.SelfLoop() {
			out[e.Head] = append(out[e.Head], int32(i))
		}
	}
	return out
}

func validateNodes(nodes []Node) error {
	for i, n := range nodes {
		if i > 0 && n.Decl < nodes[i-1].Decl {
			return ErrGraph
		}
		if n.W < 0 || n.H < 0 {
			return ErrGraph
		}
	}
	return nil
}

func (g *Graph) RebuildAdjacency() {
	g.Out = make([][]int32, len(g.Nodes))
	g.In = make([][]int32, len(g.Nodes))
	for i, e := range g.Edges {
		if e.SelfLoop() {
			continue
		}
		a, b := e.Chain()
		g.Out[a] = append(g.Out[a], int32(i))
		g.In[b] = append(g.In[b], int32(i))
	}
}
