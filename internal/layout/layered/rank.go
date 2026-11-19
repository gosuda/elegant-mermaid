package layered

import (
	"math"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type RankResult struct {
	Ranks           []int32
	BudgetExhausted bool
}

func Rank(g *Graph) ([]int32, error) {
	r, err := RankWithBudget(g)
	return r.Ranks, err
}

func RankWithBudget(g *Graph) (RankResult, error) {
	parts, err := Components(g)
	if err != nil {
		return RankResult{}, err
	}
	result := RankResult{Ranks: make([]int32, len(g.Nodes))}
	for _, members := range parts {
		component, indices := rankComponentGraph(g, members)
		ranked, err := rankComponent(component)
		if err != nil {
			return RankResult{}, err
		}
		result.BudgetExhausted = result.BudgetExhausted || ranked.BudgetExhausted
		for i, original := range indices {
			result.Ranks[original] = ranked.Ranks[i]
		}
	}
	return result, nil
}

func rankComponentGraph(g *Graph, members []int32) (*Graph, []int32) {
	included := make([]bool, len(g.Nodes))
	for _, v := range members {
		included[v] = true
	}
	component := &Graph{Params: g.Params, Direction: g.Direction, Attachments: g.Attachments, semantic: g.semantic}
	indices := make([]int32, 0, len(members))
	local := make([]int32, len(g.Nodes))
	for v, n := range g.Nodes {
		if !included[v] {
			continue
		}
		local[v] = int32(len(component.Nodes))
		component.Nodes = append(component.Nodes, n)
		indices = append(indices, int32(v))
	}
	for _, e := range g.Edges {
		if !included[e.Tail] {
			continue
		}
		e.Tail, e.Head = local[e.Tail], local[e.Head]
		component.Edges = append(component.Edges, e)
	}
	component.Clusters = componentClusters(g, included, local)
	component.Fixed = componentFixed(g, included)
	component.regions = g.regions
	return component, indices
}

func componentClusters(g *Graph, included []bool, local []int32) []Cluster {
	var clusters []Cluster
	for _, c := range g.Clusters {
		if !included[c.Top] || !included[c.Bottom] {
			continue
		}
		c.Top, c.Bottom = local[c.Top], local[c.Bottom]
		clusters = append(clusters, c)
	}
	return clusters
}

func componentFixed(g *Graph, included []bool) []FixedGroup {
	var fixed []FixedGroup
	for _, f := range g.Fixed {
		index := nodeIndex(g, f.ID)
		if index >= 0 && included[index] {
			fixed = append(fixed, f)
		}
	}
	return fixed
}

func rankComponent(g *Graph) (RankResult, error) {
	r, err := initialRanks(g)
	if err != nil {
		return RankResult{}, err
	}
	tree, err := tightTree(g, r)
	if err != nil {
		return RankResult{}, err
	}
	factor := pivotFactor()
	if factor <= 0 {
		return RankResult{}, ErrGraph
	}
	fuel := factor * int64(len(g.Nodes))
	capped := false
	for ; fuel > 0; fuel-- {
		leave, side := leavingEdge(g, tree)
		if leave < 0 {
			break
		}
		enter, delta := enteringEdge(g, r, side)
		if enter < 0 {
			return RankResult{}, ErrRanking
		}
		shiftRanks(r, side, delta)
		tree[leave], tree[enter] = false, true
	}
	if fuel == 0 && len(g.Nodes) > 0 {
		capped = true
	}
	out, err := normalizedRanks(r)
	return RankResult{Ranks: out, BudgetExhausted: capped}, err
}

func pivotFactor() int64 {
	for _, c := range gen.LayoutConst {
		if c.Name == "vector.pivot_factor" {
			return int64(c.Value)
		}
	}
	return 0
}

func initialRanks(g *Graph) ([]int64, error) {
	r := make([]int64, len(g.Nodes))
	degree := make([]int, len(g.Nodes))
	out := make([][]int, len(g.Nodes))
	for i, e := range g.Edges {
		if e.SelfLoop() {
			continue
		}
		a, b := e.Chain()
		degree[b]++
		out[a] = append(out[a], i)
	}
	done := make([]bool, len(r))
	for range r {
		v := declaredReady(g, degree, done)
		if v < 0 {
			return nil, ErrCycle
		}
		done[v] = true
		for _, i := range out[v] {
			e := g.Edges[i]
			_, b := e.Chain()
			next := r[v] + int64(e.MinLen)
			if next > math.MaxInt32 {
				return nil, geom.ErrOverflow
			}
			r[b] = max(r[b], next)
			degree[b]--
		}
	}
	return r, nil
}

func tightTree(g *Graph, r []int64) ([]bool, error) {
	tree := make([]bool, len(g.Edges))
	if len(r) == 0 {
		return tree, nil
	}
	side := make([]bool, len(r))
	side[declaredNodes(g)[0]] = true
	incident := incidentEdges(g)
	for count := 1; count < len(r); count++ {
		edge := firstTight(g, r, side, incident)
		if edge < 0 {
			i, delta := closestEdge(g, r, side)
			if i < 0 {
				return nil, ErrRanking
			}
			shiftRanks(r, side, delta)
			edge = firstTight(g, r, side, incident)
		}
		if edge < 0 {
			return nil, ErrRanking
		}
		tree[edge] = true
		e := g.Edges[edge]
		side[e.Tail], side[e.Head] = true, true
	}
	return tree, nil
}

func firstTight(g *Graph, r []int64, side []bool, incident [][]int32) int {
	for _, v := range declaredNodes(g) {
		if !side[v] {
			continue
		}
		for _, i := range incident[v] {
			e := g.Edges[i]
			if side[e.Tail] != side[e.Head] && slack(e, r) == 0 {
				return int(i)
			}
		}
	}
	return -1
}

func slack(e Edge, r []int64) int64 { a, b := e.Chain(); return r[b] - r[a] - int64(e.MinLen) }

func closestEdge(g *Graph, r []int64, side []bool) (int, int64) {
	best := -1
	gap := int64(math.MaxInt64)
	delta := int64(0)
	for i, e := range g.Edges {
		a, b := e.Chain()
		if side[a] == side[b] {
			continue
		}
		s := slack(e, r)
		if s < gap {
			best, gap = i, s
			delta = s
			if side[b] {
				delta = -s
			}
		}
	}
	return best, delta
}

func shiftRanks(r []int64, side []bool, delta int64) {
	for i := range r {
		if side[i] {
			r[i] += delta
		}
	}
}

func treeSide(g *Graph, tree []bool, removed int) []bool {
	side := make([]bool, len(g.Nodes))
	_, head := g.Edges[removed].Chain()
	side[head] = true
	queue := []int32{head}
	incident := incidentEdges(g)
	for len(queue) > 0 {
		v := queue[0]
		queue = queue[1:]
		for _, i := range incident[v] {
			if int(i) == removed || !tree[i] {
				continue
			}
			e := g.Edges[i]
			next := e.Tail
			if next == v {
				next = e.Head
			}
			if !side[next] {
				side[next] = true
				queue = append(queue, next)
			}
		}
	}
	return side
}

func cutValue(g *Graph, side []bool) int64 {
	var cut int64
	for _, e := range g.Edges {
		a, b := e.Chain()
		if side[a] == side[b] {
			continue
		}
		if side[b] {
			cut++
		} else {
			cut--
		}
	}
	return cut
}

func leavingEdge(g *Graph, tree []bool) (int, []bool) {
	for i, on := range tree {
		if !on {
			continue
		}
		side := treeSide(g, tree, i)
		if cutValue(g, side) < 0 {
			return i, side
		}
	}
	return -1, nil
}

func enteringEdge(g *Graph, r []int64, side []bool) (int, int64) {
	best := -1
	gap := int64(math.MaxInt64)
	for i, e := range g.Edges {
		a, b := e.Chain()
		if !side[a] || side[b] {
			continue
		}
		s := slack(e, r)
		if s < gap {
			best, gap = i, s
		}
	}
	return best, gap
}

func normalizedRanks(r []int64) ([]int32, error) {
	out := make([]int32, len(r))
	lo := int64(math.MaxInt64)
	for _, v := range r {
		lo = min(lo, v)
	}
	for i, v := range r {
		v -= lo
		if v > math.MaxInt32 {
			return nil, geom.ErrOverflow
		}
		out[i] = int32(v)
	}
	return out, nil
}

func Components(g *Graph) ([][]int32, error) {
	if err := validateGraph(g); err != nil {
		return nil, err
	}
	seen := make([]bool, len(g.Nodes))
	incident := incidentEdges(g)
	var parts [][]int32
	for _, root := range declaredNodes(g) {
		if seen[root] {
			continue
		}
		parts = append(parts, componentNodes(g, int32(root), incident, seen))
	}
	return parts, nil
}

func componentNodes(g *Graph, root int32, incident [][]int32, seen []bool) []int32 {
	seen[root] = true
	queue := []int32{root}
	for at := 0; at < len(queue); at++ {
		v := queue[at]
		for _, i := range incident[v] {
			e := g.Edges[i]
			next := e.Tail
			if next == v {
				next = e.Head
			}
			if !seen[next] {
				seen[next] = true
				queue = append(queue, next)
			}
		}
	}
	return queue
}
