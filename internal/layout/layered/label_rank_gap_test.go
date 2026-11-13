package layered

import (
	"reflect"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func labelChain(t *testing.T, label bool) routedCase {
	t.Helper()
	params, err := DefaultParams(scene.ProfileVector)
	if err != nil {
		t.Fatal(err)
	}
	g := &Graph{Params: params}
	g.Nodes = []Node{{Decl: 0, W: 2048, H: 1280}, {Decl: 1, W: 2048, H: 1280}}
	g.Edges = []Edge{{Tail: 0, Head: 1, Decl: 0, MinLen: 2}}
	rank, err := Rank(g)
	if err != nil {
		t.Fatal(err)
	}
	p, err := Normalize(g, rank)
	if err != nil {
		t.Fatal(err)
	}
	layers := [][]int32{{0}, {2}, {1}}
	if label {
		p.Nodes[2].Label = &EdgeLabel{W: 1024, H: 1280}
		p.Nodes[2].W, p.Nodes[2].H = 1024, 1280
	}
	return routeCase(t, p, layers)
}
func TestLabelRankHalvesRankGap(t *testing.T) {
	if got := labelChain(t, true).top; !reflect.DeepEqual(got, []int32{0, 3584, 7168}) {
		t.Fatal("each gap is 1280 + half of rank_gap 3072 + one slot of 768", got)
	}
	if got := labelChain(t, false).top; !reflect.DeepEqual(got, []int32{0, 4352, 7424}) {
		t.Fatal("a dummy-only rank keeps the full rank_gap", got)
	}
}
func TestRealNodeKeepsFullRankGap(t *testing.T) {
	p, layers := handProper(t, 3, [][2]int32{{0, 1}, {1, 2}, {0, 2}})
	for _, v := range layers[1] {
		if p.Nodes[v].Dummy {
			p.Nodes[v].Label = &EdgeLabel{W: 1024, H: 1280}
			p.Nodes[v].W, p.Nodes[v].H = 1024, 1280
		}
	}
	if got := routeCase(t, p, layers).top; got[1] != 5120 {
		t.Fatal("a rank that holds a real node is not a label rank", got)
	}
}
func TestHalfGapKeepsProfileSlotLinesAboveNextRank(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		params, err := DefaultParams(profile)
		if err != nil {
			t.Fatal(err)
		}
		if params.Slot/2 >= (params.RankGap+1)/2 {
			t.Fatal("slot lines must stay above the next rank top", profile, params)
		}
	}
}
func labelEveryChain(p *Proper) {
	for _, chain := range p.Chains {
		if len(chain) >= 3 {
			v := chain[(len(chain)-1)/2]
			p.Nodes[v].Label = &EdgeLabel{W: 1024, H: 1280}
			p.Nodes[v].W, p.Nodes[v].H = 1024, 1280
		}
	}
}
func TestHalfGapKeepsSlotLinesAboveNextRank(t *testing.T) {
	for i := range 100 {
		p, layers := coordinateCase(t, i)
		labelEveryChain(p)
		c := routeCase(t, p, layers)
		checkBands(t, c)
		heights := rankHeights(p, layers)
		for k, gap := range c.r.Gaps {
			line := c.top[k] + heights[k] + p.Slot*gap.Slots + p.Slot/2
			if gap.Slots > 0 && line >= c.top[k+1] {
				t.Fatal("slot line below the next rank top", i, k, line, c.top[k+1])
			}
		}
	}
}
