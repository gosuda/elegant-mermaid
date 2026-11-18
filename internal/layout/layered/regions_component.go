package layered

import (
	"cmp"
	"slices"
)

type componentRegions struct {
	clusters []Cluster
	index    map[string]int
	parents  []int
	sets     []localRegionSet
	lineH    int32
	minimum  regionConstraints
}

func newComponentRegions(g *Graph) (*componentRegions, error) {
	if len(g.regions.sets) == 0 {
		return nil, nil
	}
	r := &componentRegions{clusters: g.Clusters, index: make(map[string]int, len(g.Clusters)), parents: make([]int, len(g.Clusters)), lineH: g.regions.lineH}
	for i, c := range g.Clusters {
		r.index[c.ID] = i
	}
	for i, c := range g.Clusters {
		r.parents[i] = r.group(c.Parent)
	}
	for _, set := range g.regions.sets {
		parent, ok := r.index[set.parent]
		if !ok {
			continue
		}
		local := localRegionSet{parent: parent, regions: make([]int, len(set.regions))}
		for i, id := range set.regions {
			region, ok := r.index[id]
			if !ok {
				return nil, ErrGraph
			}
			local.regions[i] = region
		}
		r.sets = append(r.sets, local)
	}
	if len(r.sets) == 0 {
		return nil, nil
	}
	return r, nil
}

func (r *componentRegions) group(id string) int {
	if group, ok := r.index[id]; ok {
		return group
	}
	return -1
}

func (r *componentRegions) scope(parent string) (int, bool) {
	if parent == "" {
		return len(r.clusters), true
	}
	group, ok := r.index[parent]
	return group, ok
}

func (r *componentRegions) ancestors(parent string) []int {
	var chain []int
	for group := r.group(parent); group >= 0; group = r.parents[group] {
		chain = append(chain, group)
	}
	return chain
}

func (r *componentRegions) region(group int) bool {
	for _, set := range r.sets {
		if slices.Contains(set.regions, group) {
			return true
		}
	}
	return false
}

func sharedRegion(g *Graph, tailParent, headParent string) (string, error) {
	r, err := newComponentRegions(g)
	if err != nil || r == nil {
		return "", err
	}
	head := r.ancestors(headParent)
	for _, group := range r.ancestors(tailParent) {
		if slices.Contains(head, group) && r.region(group) {
			return r.clusters[group].ID, nil
		}
	}
	return "", nil
}

func (r *componentRegions) rank(g *Graph) (RankResult, error) {
	if r == nil {
		return RankWithBudget(g)
	}
	representatives := make([]int32, len(g.Nodes))
	for i := range representatives {
		representatives[i] = int32(i)
	}
	for _, set := range r.sets {
		first := r.clusters[set.regions[0]]
		for _, region := range set.regions {
			c := r.clusters[region]
			representatives[c.Top], representatives[c.Bottom] = first.Top, first.Bottom
		}
	}
	return rankEquivalent(g, representatives)
}

func regionCandidateCycles(g *Graph, candidate int) {
	flags := make([]bool, len(g.Edges))
	if candidate == 2 {
		flags = groupGreedyFlags(g)
	}
	for i := range g.Edges {
		g.Edges[i].Reversed = flags[i]
	}
	g.RebuildAdjacency()
}

func condenseNodes(g *Graph, representatives []int32) (*Graph, []int32, error) {
	remap := make([]int32, len(g.Nodes))
	condensed := &Graph{Params: g.Params, Direction: g.Direction}
	for i, root := range representatives {
		if int(root) == i {
			remap[i] = int32(len(condensed.Nodes))
			condensed.Nodes = append(condensed.Nodes, g.Nodes[i])
		}
	}
	for i, root := range representatives {
		if representatives[root] != root {
			return nil, nil, ErrGraph
		}
		remap[i] = remap[root]
	}
	return condensed, remap, nil
}

func condenseEdges(g, condensed *Graph, remap []int32) ([]int, error) {
	originals := make([]int, 0, len(g.Edges))
	for i, e := range g.Edges {
		if e.Tail == e.Head {
			continue
		}
		e.Tail, e.Head = remap[e.Tail], remap[e.Head]
		if e.Tail == e.Head {
			return nil, ErrGraph
		}
		originals = append(originals, i)
		condensed.Edges = append(condensed.Edges, e)
	}
	return originals, nil
}

func rankEquivalent(g *Graph, representatives []int32) (RankResult, error) {
	condensed, remap, err := condenseNodes(g, representatives)
	if err != nil {
		return RankResult{}, err
	}
	originals, err := condenseEdges(g, condensed, remap)
	if err != nil {
		return RankResult{}, err
	}
	if err := orientRankEdges(condensed, g, originals); err != nil {
		return RankResult{}, err
	}
	ranked, err := RankWithBudget(condensed)
	if err != nil {
		return RankResult{}, err
	}
	result := RankResult{Ranks: make([]int32, len(g.Nodes)), BudgetExhausted: ranked.BudgetExhausted}
	for i, node := range remap {
		result.Ranks[i] = ranked.Ranks[node]
	}
	return result, nil
}

func orientRankEdges(condensed, g *Graph, originals []int) error {
	n := len(condensed.Nodes)
	search := reachability{out: make([][]int32, n), seen: make([]uint32, n), queue: make([]int32, 0, n)}
	for i := range condensed.Edges {
		e := &condensed.Edges[i]
		if !e.Synthetic {
			continue
		}
		e.Reversed = false
		if search.path(e.Head, e.Tail) {
			return ErrGraph
		}
		search.out[e.Tail] = append(search.out[e.Tail], e.Head)
	}
	for i := range condensed.Edges {
		e := &condensed.Edges[i]
		if !e.Synthetic {
			e.Reversed = search.insert(*e)
		}
		g.Edges[originals[i]].Reversed = e.Reversed
	}
	g.RebuildAdjacency()
	return nil
}

type regionRow struct {
	group int
	rank  int32
}

func (r *componentRegions) constrain(p *Proper) error {
	if r == nil {
		return nil
	}
	reservations := make([]regionReservation, 0, len(p.Clusters))
	for _, c := range p.Clusters {
		group := r.group(c.ID)
		if group < 0 {
			return ErrGraph
		}
		reservations = append(reservations, regionReservation{group: group, right: c.TitleSize.W, span: rankSpan{first: p.Rank[c.Top], last: p.Rank[c.Bottom]}})
	}
	rows, err := r.rowReservations(p)
	if err != nil {
		return err
	}
	r.minimum, err = solveRegions(regionProblem{parents: r.parents, sets: r.sets, reservations: append(reservations, rows...), minima: frameMinima{border: p.ClusterBorder, padding: p.ClusterPad, title: r.lineH}})
	return err
}

func (r *componentRegions) rowReservations(p *Proper) ([]regionReservation, error) {
	widths := make(map[regionRow]int32)
	for v, node := range p.Nodes {
		if node.Parent == "" {
			continue
		}
		group := r.group(node.Parent)
		if group < 0 {
			return nil, ErrGraph
		}
		key := regionRow{group: group, rank: p.Rank[v]}
		width, err := coordinate(int64(widths[key]) + int64(node.W) + int64(p.NodeGap))
		if err != nil {
			return nil, err
		}
		widths[key] = width
	}
	rows := make([]regionReservation, 0, len(widths))
	for key, width := range widths {
		rows = append(rows, regionReservation{group: key.group, right: width, span: rankSpan{first: key.rank, last: key.rank}})
	}
	slices.SortFunc(rows, func(a, b regionReservation) int {
		if d := cmp.Compare(a.group, b.group); d != 0 {
			return d
		}
		return cmp.Compare(a.span.first, b.span.first)
	})
	return rows, nil
}
