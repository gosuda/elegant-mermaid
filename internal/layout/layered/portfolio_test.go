package layered

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestPortfolio(t *testing.T) {
	params, err := DefaultParams(scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	g := &Graph{Nodes: []Node{{ID: "A", Decl: 0, W: 4, H: 4}, {ID: "B", Decl: 1, W: 4, H: 4}}, Edges: []Edge{{Tail: 0, Head: 1, MinLen: 1}}, Params: params}
	part := Layout{Boxes: []Box{{ID: "A", Rect: geom.Rect{W: 4, H: 4}}, {ID: "B", Rect: geom.Rect{Y: 8, W: 4, H: 4}}}, Routes: []EdgeRoute{{Original: 0, Points: []geom.Point{{X: 2, Y: 4}, {X: 2, Y: 8}}}}}
	score, err := softCost(g, part)
	if err != nil {
		t.Fatal(err)
	}
	if score != 2 {
		t.Fatalf("N2 M4 T4 K48: 4/4+48/(16*2)=2; got %d", score)
	}
	first, err := Portfolio(g, 1)
	if err != nil {
		t.Fatal(err)
	}
	all, err := Portfolio(g, 5)
	if err != nil {
		t.Fatal(err)
	}
	for i, b := range first.Boxes {
		if b.Rect != all.Boxes[i].Rect {
			t.Fatal("equal candidates replaced the incumbent", first, all)
		}
	}
}

func TestPortfolioStrictReplacementMargin(t *testing.T) {
	cases := []struct {
		incumbent, candidate int64
		want                 bool
	}{
		{100, 100, false}, {100, 97, false}, {100, 96, true}, {0, 0, false},
	}
	for _, c := range cases {
		got, err := portfolioImproves(c.incumbent, c.candidate)
		if err != nil || got != c.want {
			t.Fatalf("%v: %v %v", c, got, err)
		}
	}
}
