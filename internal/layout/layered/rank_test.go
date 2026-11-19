package layered

import (
	"fmt"
	"math"
	"strings"
	"testing"

	randgen "github.com/gosuda/elegant-mermaid/tools/randgraph/gen"
)

func generatedGraph(t *testing.T, i int) *Graph {
	t.Helper()
	src, err := randgen.Source("layered", i)
	if err != nil {
		t.Fatal(err)
	}
	g := &Graph{}
	for line := range strings.SplitSeq(src, "\n") {
		var a, b int
		if _, err := fmt.Sscanf(line, "n%d --> n%d", &a, &b); err == nil {
			g.Edges = append(g.Edges, Edge{Tail: int32(a), Head: int32(b), MinLen: 1, Decl: int32(len(g.Edges))})
		} else if strings.Contains(line, "[") {
			g.Nodes = append(g.Nodes, Node{Decl: int32(len(g.Nodes))})
		}
	}
	return g
}

func bruteCost(g *Graph) int64 {
	best := int64(math.MaxInt64)
	r := make([]int32, len(g.Nodes))
	bound := int32(2 * (len(r) - 1))
	var visit func(int)
	visit = func(i int) {
		if !partialFeasible(g, r, i) {
			return
		}
		if i == len(r) {
			best = min(best, oracleCost(g, r))
			return
		}
		for v := int32(0); v <= bound; v++ {
			r[i] = v
			visit(i + 1)
		}
	}
	visit(0)
	return best
}

func oracleCost(g *Graph, r []int32) int64 {
	var cost int64
	for _, e := range g.Edges {
		if e.SelfLoop() {
			continue
		}
		a, b := e.Chain()
		cost += int64(r[b]) - int64(r[a])
	}
	return cost
}

func partialFeasible(g *Graph, r []int32, assigned int) bool {
	for _, e := range g.Edges {
		if e.SelfLoop() {
			continue
		}
		a, b := e.Chain()
		if int(a) < assigned && int(b) < assigned && r[b]-r[a] < e.MinLen {
			return false
		}
	}
	return true
}

func assertOptimal(t *testing.T, g *Graph) {
	t.Helper()
	result, err := RankWithBudget(g)
	if err != nil {
		t.Fatal(err)
	}
	var cost int64
	for _, e := range g.Edges {
		if e.SelfLoop() {
			continue
		}
		a, b := e.Chain()
		d := result.Ranks[b] - result.Ranks[a]
		if d < e.MinLen {
			t.Fatalf("infeasible %v", result)
		}
		cost += int64(d)
	}
	lo := int32(math.MaxInt32)
	for _, r := range result.Ranks {
		lo = min(lo, r)
	}
	if lo != 0 {
		t.Fatal(result)
	}
	if !result.BudgetExhausted && cost != bruteCost(g) {
		t.Fatalf("cost %d != optimum %d; graph %+v ranks %v", cost, bruteCost(g), g, result.Ranks)
	}
}

func TestRankOracle(t *testing.T) {
	count := 0
	for i := range 2000 {
		g := generatedGraph(t, i)
		if len(g.Nodes) > 5 {
			continue
		}
		assertOptimal(t, g)
		count++
		if count == 100 {
			break
		}
	}
	if count != 100 {
		t.Fatalf("only %d cases", count)
	}
}

func TestCyclicRankOracle(t *testing.T) {
	s := uint32(1)
	for sample := range 24 {
		n := 2 + sample%6
		g := &Graph{Nodes: make([]Node, n)}
		for i := range g.Nodes {
			g.Nodes[i].Decl = int32(i)
		}
		for i := range n + 2 {
			s ^= s << 13
			s ^= s >> 17
			s ^= s << 5
			a := int32(s % uint32(n))
			s ^= s << 13
			s ^= s >> 17
			s ^= s << 5
			b := int32(s % uint32(n))
			g.Edges = append(g.Edges, Edge{Tail: a, Head: b, MinLen: 1, Decl: int32(i)})
		}
		if _, err := BreakCycles(g); err != nil {
			t.Fatal(err)
		}
		assertOptimal(t, g)
	}
}

func TestRankVectors(t *testing.T) {
	for i := range 10 {
		g := generatedGraph(t, i)
		r, err := Rank(g)
		if err != nil {
			t.Fatal(err)
		}
		t.Logf("case %d: %v", i, r)
	}
}
