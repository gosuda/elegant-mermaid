package layered

import (
	"slices"
	"testing"
)

func TestClusters(t *testing.T) {
	g := &Graph{Nodes: []Node{{ID: "A", Decl: 1, Parent: "G"}, {ID: "B", Decl: 2, Parent: "G"}}, Edges: []Edge{{Tail: 0, Head: 1, MinLen: 1}}, Clusters: []Cluster{{ID: "G", Decl: 0}}}
	clusterBorders(g)
	rank, err := Rank(g)
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Equal(rank, []int32{1, 2, 0, 3}) {
		t.Fatalf("T->A->B->B_C gives ranks0,1,2,3: %v", rank)
	}
	empty := &Graph{Clusters: []Cluster{{ID: "empty"}}}
	clusterBorders(empty)
	rank, err = Rank(empty)
	if err != nil {
		t.Fatal(err)
	}
	if !slices.Equal(rank, []int32{0, 1}) || len(empty.Edges) != 1 || empty.Edges[0].MinLen != 1 {
		t.Fatal("empty cluster must retain synthetic positive span", empty, rank)
	}
}

func TestRankingConstraintsDoNotNormalize(t *testing.T) {
	g := &Graph{Nodes: []Node{{ID: "A", Decl: 1, Parent: "G", W: 5, H: 3}, {ID: "B", Decl: 2, Parent: "G", W: 5, H: 3}}, Edges: []Edge{{Tail: 0, Head: 1, MinLen: 1}}, Clusters: []Cluster{{ID: "G", Decl: 0}}}
	clusterBorders(g)
	rank, err := Rank(g)
	if err != nil {
		t.Fatal(err)
	}
	p, err := Normalize(g, rank)
	if err != nil {
		t.Fatal(err)
	}
	for _, n := range p.Nodes {
		if n.Dummy {
			t.Fatal("ranking-only constraint created a dummy", n)
		}
	}
	for _, e := range p.Edges {
		if e.Original > 0 {
			t.Fatal("ranking constraint survived normalization", e)
		}
	}
}
