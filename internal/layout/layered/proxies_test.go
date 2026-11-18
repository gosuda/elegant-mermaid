package layered

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestGroupProxyAliases(t *testing.T) {
	in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "S", Role: scene.RoleGroup}, {ID: "A", Parent: "S"}, {ID: "X"}}, Labels: []scene.Label{{ID: "S.label", Owner: "S", Text: "S"}}, Routes: []scene.Route{
		{ID: "entry", From: "S", To: "A"}, {ID: "exit", From: "A", To: "S"}, {ID: "out", From: "S", To: "X"}, {ID: "in", From: "X", To: "S"}, {ID: "self", From: "S", To: "S"},
	}}
	options := scene.DefaultOptions()
	options.Profile = scene.ProfileCell
	g, _, err := measuredGraph(in, options)
	if err != nil {
		t.Fatal(err)
	}
	top, bottom := g.Clusters[0].Top, g.Clusters[0].Bottom
	a, x := nodeIndex(g, "A"), nodeIndex(g, "X")
	want := [][2]int32{{top, a}, {a, bottom}, {bottom, x}, {x, top}, {bottom, bottom}}
	for i, pair := range want {
		if g.Edges[i].Tail != pair[0] || g.Edges[i].Head != pair[1] {
			t.Fatalf("proxy %d: %v, want %v", i, g.Edges[i], pair)
		}
	}
	if nodeIndex(g, "S") >= 0 || g.Edges[4].FrameLoop != "S" {
		t.Fatal("proxy became a model node or frame loop lost", g)
	}
}

func protectedCycleGraph() *Graph {
	return &Graph{Nodes: []Node{{Decl: 0}, {Decl: 1}, {Decl: 2}}, Edges: []Edge{
		{Tail: 2, Head: 0, MinLen: 1, Decl: 0}, {Tail: 0, Head: 1, MinLen: 1, Decl: 1, Synthetic: true}, {Tail: 1, Head: 2, MinLen: 1, Decl: 2, Synthetic: true},
	}}
}

func assertProtectedOrientation(t *testing.T, g *Graph) {
	t.Helper()
	if !g.Edges[0].Reversed || g.Edges[1].Reversed || g.Edges[2].Reversed {
		t.Fatal("only semantic closing edge may reverse", g.Edges)
	}
	ranks, err := Rank(g)
	if err != nil {
		t.Fatal(err)
	}
	if ranks[0] != 0 || ranks[1] != 1 || ranks[2] != 2 {
		t.Fatal("immutable synthetic chain must stay feasible", ranks)
	}
}

func TestProtectedCompoundCycles(t *testing.T) {
	g := protectedCycleGraph()
	if _, err := BreakCycles(g); err != nil {
		t.Fatal(err)
	}
	assertProtectedOrientation(t, g)
}

func TestGreedyProtectedConstraints(t *testing.T) {
	g := protectedCycleGraph()
	if err := candidateCycles(g, 2); err != nil {
		t.Fatal(err)
	}
	assertProtectedOrientation(t, g)
}
