package layered

import (
	"cmp"
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type OrderStart uint8

const (
	OrderStartDeclaration OrderStart = iota
	OrderStartBreadthFirst
	OrderStartReverse
)

type OrderKey uint8

const (
	OrderKeyBarycentre OrderKey = iota
	OrderKeyMedian
)

type OrderOptions struct {
	Start OrderStart
	Key   OrderKey
}
type OrderResult struct {
	Layers          [][]int32
	BudgetExhausted bool
}
type (
	orderFraction struct{ sum, count int64 }
	orderGraph    struct {
		p            *Proper
		above, below [][]int32
		key          OrderKey
	}
)

func Order(p *Proper, opts OrderOptions) ([][]int32, error) {
	r, err := OrderWithBudget(p, opts)
	return r.Layers, err
}

func OrderWithBudget(p *Proper, opts OrderOptions) (OrderResult, error) {
	if opts.Start > OrderStartReverse || opts.Key > OrderKeyMedian {
		return OrderResult{}, ErrGraph
	}
	g, layers, err := orderPrepare(p)
	if err != nil {
		return OrderResult{}, err
	}
	g.key = opts.Key
	seed := orderClone(layers)
	startLayers(p, seed, opts.Start)
	for i := range layers {
		layers[i] = g.clusterLayer(layers[i], "", nil)
		seed[i] = g.clusterLayer(seed[i], "", nil)
	}
	if err := g.siblingNormalise(layers); err != nil {
		return OrderResult{}, err
	}
	if err := g.siblingNormalise(seed); err != nil {
		return OrderResult{}, err
	}
	if g.crossCount(seed) < g.crossCount(layers) {
		layers = seed
	}
	return g.orderRun(layers, orderConstant("vector.sweep_max"), orderConstant("vector.sweep_stall"))
}

func orderConstant(name string) int {
	for _, row := range gen.LayoutConst {
		if row.Name == name {
			return int(row.Value)
		}
	}
	return 0
}

func orderPrepare(p *Proper) (orderGraph, [][]int32, error) {
	g := orderGraph{p: p}
	if err := validateOrderGraph(p); err != nil {
		return g, nil, err
	}
	maxRank, err := orderMaxRank(p)
	if err != nil {
		return g, nil, err
	}
	layers := make([][]int32, int(maxRank)+1)
	for i, r := range p.Rank {
		layers[r] = append(layers[r], int32(i))
	}
	for _, layer := range layers {
		slices.SortStableFunc(layer, func(a, b int32) int {
			return orderDeclarationCompare(p, a, b)
		})
	}
	g.above = make([][]int32, len(p.Nodes))
	g.below = make([][]int32, len(p.Nodes))
	for _, e := range p.Edges {
		if err := g.orderEdge(e); err != nil {
			return g, nil, err
		}
	}
	return g, layers, nil
}

func validateOrderGraph(p *Proper) error {
	if p == nil || len(p.Nodes) != len(p.Rank) || len(p.Nodes) > math.MaxInt32 || len(p.Edges) > math.MaxInt32 {
		return ErrGraph
	}
	return nil
}

func orderDeclarationCompare(p *Proper, a, b int32) int {
	if c := cmp.Compare(p.Nodes[a].Decl, p.Nodes[b].Decl); c != 0 {
		return c
	}
	return cmp.Compare(a, b)
}

func orderMaxRank(p *Proper) (int32, error) {
	maxRank := int32(-1)
	for _, r := range p.Rank {
		if r < 0 || int64(r) > int64(len(p.Nodes)) {
			return 0, ErrRanking
		}
		maxRank = max(maxRank, r)
	}
	return maxRank, nil
}

func (g *orderGraph) orderEdge(e ProperEdge) error {
	if e.Tail < 0 || e.Head < 0 || int(e.Tail) >= len(g.p.Nodes) || int(e.Head) >= len(g.p.Nodes) {
		return ErrGraph
	}
	if int64(g.p.Rank[e.Head])-int64(g.p.Rank[e.Tail]) != 1 {
		return ErrRanking
	}
	g.below[e.Tail] = append(g.below[e.Tail], e.Head)
	g.above[e.Head] = append(g.above[e.Head], e.Tail)
	return nil
}

func orderClone(layers [][]int32) [][]int32 {
	out := make([][]int32, len(layers))
	for i, l := range layers {
		out[i] = slices.Clone(l)
	}
	return out
}

func (g orderGraph) orderRun(best [][]int32, limit, stallLimit int) (OrderResult, error) {
	if limit <= 0 || stallLimit <= 0 {
		return OrderResult{}, ErrGraph
	}
	score := g.crossCount(best)
	stall := 0
	for sweep := range limit {
		trial := orderClone(best)
		if err := g.orderSweep(trial, sweep); err != nil {
			return OrderResult{}, err
		}
		if err := g.orderTranspose(trial); err != nil {
			return OrderResult{}, err
		}
		if err := g.siblingNormalise(trial); err != nil {
			return OrderResult{}, err
		}
		next := g.crossCount(trial)
		stall++
		if next < score {
			best = trial
			score = next
			stall = 0
		}
		if sweep+1 == limit {
			return OrderResult{best, true}, nil
		}
		if stall >= stallLimit {
			return OrderResult{Layers: best}, nil
		}
	}
	return OrderResult{Layers: best}, nil
}

func orderPositions(layers [][]int32, n int) []int64 {
	pos := make([]int64, n)
	for _, l := range layers {
		for i, v := range l {
			pos[v] = int64(i)
		}
	}
	return pos
}

func (g orderGraph) orderSweep(layers [][]int32, sweep int) error {
	start, step := 1, 1
	neighbours := g.above
	if sweep%2 != 0 {
		start, step = len(layers)-2, -1
		neighbours = g.below
	}
	pos := orderPositions(layers, len(g.p.Nodes))
	for k := range max(0, len(layers)-1) {
		r := start + k*step
		if err := g.sortLayer(layers[r], neighbours, pos); err != nil {
			return err
		}
		for i, v := range layers[r] {
			pos[v] = int64(i)
		}
	}
	return nil
}

func orderSort(layer []int32, neighbours [][]int32, pos []int64) error {
	keys := make([]orderFraction, len(pos))
	for _, v := range layer {
		key := orderFraction{count: int64(len(neighbours[v]))}
		for _, u := range neighbours[v] {
			if key.sum > math.MaxInt64-pos[u] {
				return geom.ErrOverflow
			}
			key.sum += pos[u]
		}
		if key.count == 0 {
			key = orderFraction{pos[v], 1}
		}
		keys[v] = key
	}
	var sortErr error
	slices.SortStableFunc(layer, func(a, b int32) int {
		result, err := orderCompare(keys[a], keys[b])
		if err != nil {
			sortErr = err
		}
		return result
	})
	return sortErr
}

func orderCompare(a, b orderFraction) (int, error) {
	if a.sum > math.MaxInt64/b.count || b.sum > math.MaxInt64/a.count {
		return 0, geom.ErrOverflow
	}
	return cmp.Compare(a.sum*b.count, b.sum*a.count), nil
}

func (g orderGraph) crossCount(layers [][]int32) int64 {
	pos := orderPositions(layers, len(g.p.Nodes))
	var total int64
	for r := 1; r < len(layers); r++ {
		total += g.crossPair(layers[r-1], len(layers[r]), pos)
	}
	return total
}

func (g orderGraph) crossPair(upper []int32, width int, pos []int64) int64 {
	tree := make([]int64, width+1)
	var seen, total int64
	for _, v := range upper {
		for _, u := range g.below[v] {
			total += seen - crossPrefix(tree, int(pos[u])+1)
		}
		for _, u := range g.below[v] {
			crossAdd(tree, int(pos[u])+1)
			seen++
		}
	}
	return total
}

func crossPrefix(tree []int64, i int) int64 {
	var sum int64
	for i > 0 {
		sum += tree[i]
		i -= i & -i
	}
	return sum
}

func crossAdd(tree []int64, i int) {
	for i < len(tree) {
		tree[i]++
		i += i & -i
	}
}

func (g orderGraph) orderTranspose(layers [][]int32) error {
	c0 := g.crossCount(layers)
	if c0 == math.MaxInt64 {
		return geom.ErrOverflow
	}
	fuel := c0 + 1
	for range fuel {
		if !g.orderTransposePass(layers) {
			break
		}
	}
	return nil
}

func (g orderGraph) orderTransposePass(layers [][]int32) bool {
	pos := orderPositions(layers, len(g.p.Nodes))
	changed := false
	for _, layer := range layers {
		for i := 1; i < len(layer); i++ {
			a, b := layer[i-1], layer[i]
			if !transposePeers(g.p.Nodes[a], g.p.Nodes[b]) {
				continue
			}
			delta := crossSwapDelta(g.above[a], g.above[b], pos) + crossSwapDelta(g.below[a], g.below[b], pos)
			if delta < 0 {
				layer[i-1], layer[i] = b, a
				pos[a], pos[b] = pos[b], pos[a]
				changed = true
			}
		}
	}
	return changed
}

func crossSwapDelta(a, b []int32, pos []int64) int64 {
	var delta int64
	for _, u := range a {
		for _, v := range b {
			delta += int64(cmp.Compare(pos[v], pos[u]))
		}
	}
	return delta
}
