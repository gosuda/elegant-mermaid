package layered

import (
	"cmp"
	"slices"
)

type clusterBlock struct {
	nodes []int32
	key   orderFraction
	decl  int32
	index int
}
type orderWeights struct {
	neighbours [][]int32
	positions  []int64
	err        error
}

func transposePeers(a, b ProperNode) bool {
	return a.Parent == b.Parent && a.Border == BorderNone && b.Border == BorderNone
}

func (g orderGraph) sortLayer(layer []int32, neighbours [][]int32, pos []int64) error {
	if len(g.p.Clusters) == 0 && g.key == OrderKeyBarycentre {
		return orderSort(layer, neighbours, pos)
	}
	weights := orderWeights{neighbours: neighbours, positions: pos}
	copy(layer, g.clusterLayer(layer, "", &weights))
	return weights.err
}

func (g orderGraph) clusterLayer(layer []int32, parent string, weights *orderWeights) []int32 {
	left, right, blocks := g.layerMembers(layer, parent, weights)
	for _, c := range g.p.Clusters {
		if c.Parent != parent {
			continue
		}
		nodes := g.clusterLayer(layer, c.ID, weights)
		if len(nodes) > 0 {
			blocks = append(blocks, g.block(nodes, weights, len(blocks)))
		}
	}
	sortBlocks(layer, blocks, weights)
	out := slices.Clone(left)
	for _, b := range blocks {
		out = append(out, b.nodes...)
	}
	return append(out, right...)
}

func (g orderGraph) layerMembers(layer []int32, parent string, weights *orderWeights) ([]int32, []int32, []clusterBlock) {
	var left, right []int32
	var blocks []clusterBlock
	for _, v := range layer {
		n := g.p.Nodes[v]
		if n.Parent != parent {
			continue
		}
		switch n.Border {
		case BorderLeft:
			left = append(left, v)
		case BorderRight:
			right = append(right, v)
		default:
			blocks = append(blocks, g.block([]int32{v}, weights, len(blocks)))
		}
	}
	return left, right, blocks
}

func sortBlocks(layer []int32, blocks []clusterBlock, weights *orderWeights) {
	if weights != nil {
		slices.SortStableFunc(blocks, func(a, b clusterBlock) int { return compareBlocks(weights, a, b) })
		return
	}
	for i := range blocks {
		blocks[i].index = blockStart(layer, blocks[i].nodes)
	}
	slices.SortStableFunc(blocks, func(a, b clusterBlock) int { return cmp.Compare(a.index, b.index) })
}

func compareBlocks(weights *orderWeights, a, b clusterBlock) int {
	comparison, err := orderCompare(a.key, b.key)
	if err != nil {
		weights.err = err
	}
	if comparison != 0 {
		return comparison
	}
	if d := cmp.Compare(a.decl, b.decl); d != 0 {
		return d
	}
	return cmp.Compare(a.index, b.index)
}

func (g orderGraph) block(nodes []int32, weights *orderWeights, index int) clusterBlock {
	block := clusterBlock{nodes: nodes, decl: g.p.Nodes[nodes[0]].Decl, index: index}
	for _, v := range nodes {
		block.decl = min(block.decl, g.p.Nodes[v].Decl)
	}
	if weights == nil {
		return block
	}
	values := blockValues(nodes, weights)
	if g.key == OrderKeyMedian && len(nodes) == 1 {
		slices.Sort(values)
		block.key = orderFraction{values[(len(values)-1)/2], 1}
		return block
	}
	arithmetic := coordinateArithmetic{}
	for _, value := range values {
		block.key.sum = arithmetic.add(block.key.sum, value)
	}
	if arithmetic.err != nil {
		weights.err = arithmetic.err
	}
	block.key.count = int64(len(values))
	return block
}

func blockValues(nodes []int32, weights *orderWeights) []int64 {
	var values []int64
	for _, v := range nodes {
		for _, w := range weights.neighbours[v] {
			values = append(values, weights.positions[w])
		}
	}
	if len(values) > 0 {
		return values
	}
	for _, v := range nodes {
		values = append(values, weights.positions[v])
	}
	return values
}

func startLayers(p *Proper, layers [][]int32, start OrderStart) {
	if start == OrderStartReverse {
		for _, layer := range layers {
			slices.Reverse(layer)
		}
		return
	}
	if start != OrderStartBreadthFirst {
		return
	}
	discovery := breadthDiscovery(p)
	for _, layer := range layers {
		slices.SortStableFunc(layer, func(a, b int32) int { return cmp.Compare(discovery[a], discovery[b]) })
	}
}

type breadthState struct {
	order []int
	seen  []bool
	next  int
	queue []int32
}

func breadthDiscovery(p *Proper) []int {
	state := breadthState{order: make([]int, len(p.Nodes)), seen: make([]bool, len(p.Nodes)), queue: make([]int32, 0, len(p.Nodes))}
	roots := make([]int32, len(p.Nodes))
	for i := range roots {
		roots[i] = int32(i)
	}
	slices.SortStableFunc(roots, func(a, b int32) int { return orderDeclarationCompare(p, a, b) })
	if root := breadthRoot(p, roots); root >= 0 {
		state.visit(p, root)
	}
	for _, root := range roots {
		state.visit(p, root)
	}
	return state.order
}

func breadthRoot(p *Proper, roots []int32) int32 {
	for _, v := range roots {
		if len(p.In[v]) == 0 {
			return v
		}
	}
	if len(roots) > 0 {
		return roots[0]
	}
	return -1
}

func (state *breadthState) visit(p *Proper, root int32) {
	if state.seen[root] {
		return
	}
	state.queue = state.queue[:0]
	state.queue = append(state.queue, root)
	state.seen[root] = true
	for at := 0; at < len(state.queue); at++ {
		v := state.queue[at]
		state.order[v] = state.next
		state.next++
		state.queue = enqueueChildren(p, v, state.queue, state.seen)
	}
}

func enqueueChildren(p *Proper, v int32, queue []int32, seen []bool) []int32 {
	for _, i := range p.Out[v] {
		w := p.Edges[i].Head
		if !seen[w] {
			seen[w] = true
			queue = append(queue, w)
		}
	}
	return queue
}

func borderMember(p *Proper, a, b ProperNode) bool {
	if a.Border == BorderLeft || a.Border == BorderRight {
		return insideCluster(p.Clusters, b.Parent, a.Parent)
	}
	if b.Border == BorderLeft || b.Border == BorderRight {
		return insideCluster(p.Clusters, a.Parent, b.Parent)
	}
	return false
}

func blockStart(layer, nodes []int32) int {
	first := len(layer)
	for _, v := range nodes {
		first = min(first, slices.Index(layer, v))
	}
	return first
}

func ownTitleAnchor(a, b ProperNode) bool {
	if a.Parent != b.Parent {
		return false
	}
	if a.Border == BorderTitle {
		return b.Border == BorderTop || b.Border == BorderBottom
	}
	if b.Border == BorderTitle {
		return a.Border == BorderTop || a.Border == BorderBottom
	}
	return false
}
