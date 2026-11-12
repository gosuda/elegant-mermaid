package layered

import (
	"fmt"
	"reflect"
	"slices"
	"strings"
	"testing"

	random "github.com/gosuda/elegant-mermaid/tools/randgraph/gen"
)

func orderNaive(p *Proper, layers [][]int32) int64 {
	pos := orderPositions(layers, len(p.Nodes))
	var count int64
	for i, a := range p.Edges {
		for _, b := range p.Edges[i+1:] {
			if p.Rank[a.Tail] == p.Rank[b.Tail] && (pos[a.Tail]-pos[b.Tail])*(pos[a.Head]-pos[b.Head]) < 0 {
				count++
			}
		}
	}
	return count
}
func orderRandom(s *uint32) uint32 { *s ^= *s << 13; *s ^= *s >> 17; *s ^= *s << 5; return *s }
func TestOrderCrossAccumulator(t *testing.T) {
	for seed := range 200 {
		s := uint32(seed + 1)
		a := int(orderRandom(&s)%12) + 1
		b := int(orderRandom(&s)%12) + 1
		p := &Proper{Nodes: make([]ProperNode, a+b), Rank: make([]int32, a+b)}
		for i := a; i < a+b; i++ {
			p.Rank[i] = 1
		}
		for range 100 {
			p.Edges = append(p.Edges, ProperEdge{Tail: int32(orderRandom(&s) % uint32(a)), Head: int32(a) + int32(orderRandom(&s)%uint32(b))})
		}
		g, l, err := orderPrepare(p)
		if err != nil {
			t.Fatal(err)
		}
		if got, want := g.crossCount(l), orderNaive(p, l); got != want {
			t.Fatalf("seed %d: %d != %d", seed, got, want)
		}
	}
}
func orderCase(t *testing.T, index int) *Proper {
	t.Helper()
	src, err := random.Source("layered", index)
	if err != nil {
		t.Fatal(err)
	}
	g := &Graph{}
	for _, line := range strings.Split(src, "\n")[1:] {
		var a, b int
		if _, err := fmt.Sscanf(line, "n%d --> n%d", &a, &b); err == nil {
			g.Edges = append(g.Edges, Edge{Tail: int32(a), Head: int32(b), Decl: int32(len(g.Edges)), MinLen: 1})
			continue
		}
		if strings.Contains(line, "[") {
			g.Nodes = append(g.Nodes, Node{Decl: int32(len(g.Nodes))})
		}
	}
	if _, err := BreakCycles(g); err != nil {
		t.Fatal(err)
	}
	ranks, err := Rank(g)
	if err != nil {
		t.Fatal(err)
	}
	p, err := Normalize(g, ranks)
	if err != nil {
		t.Fatal(err)
	}
	return p
}
func TestOrderRandomGraphs(t *testing.T) {
	for index := range 200 {
		p := orderCase(t, index)
		g, initial, err := orderPrepare(p)
		if err != nil {
			t.Fatal(err)
		}
		got, err := Order(p, OrderOptions{})
		if err != nil {
			t.Fatal(err)
		}
		again, err := Order(p, OrderOptions{})
		if err != nil {
			t.Fatal(err)
		}
		if !reflect.DeepEqual(got, again) {
			t.Fatal("nondeterministic order")
		}
		if orderNaive(p, got) > orderNaive(p, initial) {
			t.Fatal("order worsens crossings")
		}
		orderAssertPermutation(t, initial, got)
		orderAssertTranspose(t, g, initial)
		if index < 10 {
			t.Logf("case %d: %v crossings %d -> %d", index, got, orderNaive(p, initial), orderNaive(p, got))
		}
	}
}

func orderAssertTranspose(t *testing.T, g orderGraph, initial [][]int32) {
	t.Helper()
	trial := orderClone(initial)
	for {
		before := orderNaive(g.p, trial)
		changed := g.orderTransposePass(trial)
		if orderNaive(g.p, trial) > before {
			t.Fatal("transpose worsens crossings")
		}
		if !changed {
			return
		}
	}
}
func orderAssertPermutation(t *testing.T, a, b [][]int32) {
	t.Helper()
	if len(a) != len(b) {
		t.Fatal("rank count changed")
	}
	for i := range a {
		x, y := slices.Clone(a[i]), slices.Clone(b[i])
		slices.Sort(x)
		slices.Sort(y)
		if !slices.Equal(x, y) {
			t.Fatal("rank membership changed")
		}
	}
}
func TestOrderHandGraphs(t *testing.T) {
	p := &Proper{Nodes: make([]ProperNode, 4), Rank: []int32{0, 0, 1, 1}, Edges: []ProperEdge{{Tail: 0, Head: 3}, {Tail: 1, Head: 2}}}
	got, err := Order(p, OrderOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if orderNaive(p, got) != 0 {
		t.Fatal("crossing not removed")
	}
	p = &Proper{Nodes: make([]ProperNode, 6), Rank: []int32{0, 0, 0, 1, 1, 1}}
	for a := range int32(3) {
		for b := int32(3); b < 6; b++ {
			p.Edges = append(p.Edges, ProperEdge{Tail: a, Head: b})
		}
	}
	got, err = Order(p, OrderOptions{})
	if err != nil {
		t.Fatal(err)
	}
	if orderNaive(p, got) != 9 {
		t.Fatal("K3,3 minimum is nine")
	}
}
func TestOrderBudgetAndGuards(t *testing.T) {
	p := &Proper{}
	g, l, err := orderPrepare(p)
	if err != nil {
		t.Fatal(err)
	}
	r, err := g.orderRun(l, 1, 4)
	if err != nil || !r.BudgetExhausted {
		t.Fatal("missing budget flag", err)
	}
	if _, err := Order(nil, OrderOptions{}); err == nil {
		t.Fatal("nil accepted")
	}
	if _, err := Order(p, OrderOptions{Start: 99}); err == nil {
		t.Fatal("unknown start accepted")
	}
}
