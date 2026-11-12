package layered

import (
	"slices"
	"testing"
)

func kahnAcyclic(g *Graph) bool {
	degree := make([]int, len(g.Nodes))
	out := make([][]int32, len(g.Nodes))
	for _, e := range g.Edges {
		if e.SelfLoop() {
			continue
		}
		a, b := e.Chain()
		degree[b]++
		out[a] = append(out[a], b)
	}
	queue := []int{}
	for v, d := range degree {
		if d == 0 {
			queue = append(queue, v)
		}
	}
	for at := 0; at < len(queue); at++ {
		for _, v := range out[queue[at]] {
			degree[v]--
			if degree[v] == 0 {
				queue = append(queue, int(v))
			}
		}
	}
	return len(queue) == len(g.Nodes)
}

func TestBreakCycles(t *testing.T) {
	g := &Graph{Nodes: make([]Node, 2000)}
	for i := range g.Nodes {
		g.Nodes[i].Decl = int32(i)
		g.Edges = append(g.Edges, Edge{Tail: int32(i), Head: int32((i + 1) % 2000), MinLen: 1, Decl: int32(i)})
	}
	g.Edges = append(g.Edges, Edge{Tail: 0, Head: 0, MinLen: 1, Decl: 2000})
	before := slices.Clone(g.Edges)
	reversed, err := BreakCycles(g)
	if err != nil {
		t.Fatal(err)
	}
	if !kahnAcyclic(g) {
		t.Fatal("cycle remains")
	}
	assertPreservedEdges(t, before, g.Edges)
	if !reversed[1999] || reversed[2000] {
		t.Fatal("wrong DFS reversal or reversed self loop")
	}
}

func TestDAG(t *testing.T) {
	g := generatedGraph(t, 0)
	r, err := BreakCycles(g)
	if err != nil {
		t.Fatal(err)
	}
	for _, v := range r {
		if v {
			t.Fatal("DAG edge reversed")
		}
	}
}

func TestNormalize(t *testing.T) {
	g := &Graph{Nodes: []Node{{Decl: 0}, {Decl: 1}, {Decl: 2}}, Edges: []Edge{{Tail: 0, Head: 1, MinLen: 1, Decl: 0}, {Tail: 2, Head: 0, MinLen: 1, Decl: 1, Reversed: true}, {Tail: 1, Head: 1, MinLen: 1, Decl: 2}}}
	p, err := Normalize(g, []int32{0, 2, 4})
	if err != nil {
		t.Fatal(err)
	}
	if len(p.Nodes) != 7 {
		t.Fatalf("dummy count %d", len(p.Nodes)-3)
	}
	for _, e := range p.Edges {
		if p.Rank[e.Head]-p.Rank[e.Tail] != 1 {
			t.Fatal(e)
		}
	}
	if len(p.Chains[0]) != 3 || len(p.Chains[1]) != 5 || len(p.Chains[2]) != 0 {
		t.Fatal(p.Chains)
	}
	assertDummySizes(t, g, p)
}

func TestComponents(t *testing.T) {
	g := &Graph{Nodes: []Node{{Decl: 0}, {Decl: 1}, {Decl: 2}, {Decl: 3}}, Edges: []Edge{{Tail: 2, Head: 0, MinLen: 1}}}
	parts, err := Components(g)
	if err != nil {
		t.Fatal(err)
	}
	if len(parts) != 3 || len(parts[0]) != 2 || parts[0][0] != 0 || parts[1][0] != 1 || parts[2][0] != 3 {
		t.Fatal(parts)
	}
}

func assertPreservedEdges(t *testing.T, before, after []Edge) {
	t.Helper()
	for i, e := range after {
		e.Reversed = before[i].Reversed
		if e != before[i] {
			t.Fatalf("changed edge %d", i)
		}
	}
}

func assertDummySizes(t *testing.T, g *Graph, p *Proper) {
	t.Helper()
	for _, n := range p.Nodes[len(g.Nodes):] {
		want := ProperNode{Node: Node{Decl: g.Edges[n.Edge].Decl, W: 768}, Dummy: true, Edge: n.Edge}
		if n != want {
			t.Fatal(n)
		}
	}
}
