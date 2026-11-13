package layered

import (
	"math"
	"slices"
)

const noPosition = -1

type siblingOrder struct {
	p           *Proper
	chains      [][]int
	parent      []int
	ranks       int
	left        []int64
	first, last []int32
	key         []orderFraction
	number      []int
}
type siblingItem struct {
	nodes []int32
	child int
}

func (g orderGraph) siblingNormalise(layers [][]int32) error {
	if len(g.p.Clusters) == 0 {
		return nil
	}
	s := newSiblingOrder(g.p, layers)
	for _, group := range s.groups() {
		if err := s.linearise(group); err != nil {
			return err
		}
	}
	for _, layer := range layers {
		copy(layer, s.level(layer, 0))
	}
	return nil
}

func newSiblingOrder(p *Proper, layers [][]int32) *siblingOrder {
	n := len(p.Clusters)
	s := &siblingOrder{p: p, chains: make([][]int, len(p.Nodes)), parent: make([]int, n), ranks: len(layers), first: make([]int32, n), last: make([]int32, n), key: make([]orderFraction, n), number: make([]int, n)}
	s.left = slices.Repeat([]int64{noPosition}, n*s.ranks)
	index := make(map[string]int, n)
	for i, c := range p.Clusters {
		index[c.ID] = i
		s.first[i], s.last[i] = math.MaxInt32, noPosition
	}
	for i, c := range p.Clusters {
		s.parent[i] = siblingClusterIndex(index, c.Parent)
	}
	for v, node := range p.Nodes {
		s.chains[v] = s.chain(index, node.Parent)
	}
	s.leftBorders(orderPositions(layers, len(p.Nodes)))
	return s
}

func siblingClusterIndex(index map[string]int, id string) int {
	if i, ok := index[id]; ok {
		return i
	}
	return noPosition
}

func (s *siblingOrder) chain(index map[string]int, parent string) []int {
	var chain []int
	for i := siblingClusterIndex(index, parent); i >= 0 && len(chain) < len(s.parent); i = s.parent[i] {
		chain = append(chain, i)
	}
	slices.Reverse(chain)
	return chain
}

func (s *siblingOrder) leftBorders(pos []int64) {
	for v, node := range s.p.Nodes {
		chain := s.chains[v]
		if node.Border != BorderLeft || len(chain) == 0 {
			continue
		}
		c, r := chain[len(chain)-1], s.p.Rank[v]
		s.left[c*s.ranks+int(r)] = pos[v]
		s.first[c], s.last[c] = min(s.first[c], r), max(s.last[c], r)
	}
	for c := range s.key {
		s.key[c] = s.meanKey(c)
	}
}
func (s *siblingOrder) meanKey(c int) orderFraction {
	var key orderFraction
	for r := s.first[c]; r <= s.last[c]; r++ {
		if pos := s.at(c, r); pos != noPosition {
			key.sum += pos
		}
		key.count++
	}
	key.count = max(key.count, 1)
	return key
}

func (s *siblingOrder) groups() [][]int {
	byParent := make([][]int, len(s.parent)+1)
	for c, parent := range s.parent {
		byParent[parent+1] = append(byParent[parent+1], c)
	}
	return byParent
}

func (s *siblingOrder) at(c int, r int32) int64 {
	return s.left[c*s.ranks+int(r)]
}

func (s *siblingOrder) votes(a, b int) (forward, backward int) {
	for r := max(s.first[a], s.first[b]); r <= min(s.last[a], s.last[b]); r++ {
		pa, pb := s.at(a, r), s.at(b, r)
		switch {
		case pa == noPosition || pb == noPosition:
		case pa < pb:
			forward++
		default:
			backward++
		}
	}
	return forward, backward
}

func (s *siblingOrder) precedes(a, b int) (first, related bool) {
	forward, backward := s.votes(a, b)
	if forward == backward {
		return s.p.Clusters[a].Decl < s.p.Clusters[b].Decl, forward+backward > 0
	}
	return forward > backward, true
}

func (s *siblingOrder) linearise(group []int) error {
	waiting := make([]int, len(group))
	successors := make([][]int, len(group))
	for i := range group {
		for j := i + 1; j < len(group); j++ {
			first, related := s.precedes(group[i], group[j])
			if !related {
				continue
			}
			from, to := i, j
			if !first {
				from, to = j, i
			}
			successors[from] = append(successors[from], to)
			waiting[to]++
		}
	}
	done := make([]bool, len(group))
	for number := range group {
		pick, err := s.next(group, done, waiting)
		if err != nil {
			return err
		}
		done[pick] = true
		s.number[group[pick]] = number
		for _, to := range successors[pick] {
			waiting[to]--
		}
	}
	return nil
}

func (s *siblingOrder) next(group []int, done []bool, waiting []int) (int, error) {
	pick, err := s.smallest(group, func(i int) bool { return !done[i] && waiting[i] == 0 })
	if err != nil || pick >= 0 {
		return pick, err
	}
	pick, err = s.smallest(group, func(i int) bool { return !done[i] })
	if err == nil && pick < 0 {
		err = ErrGraph
	}
	return pick, err
}

func (s *siblingOrder) smallest(group []int, eligible func(int) bool) (int, error) {
	pick := noPosition
	for i := range group {
		if !eligible(i) {
			continue
		}
		if pick == noPosition {
			pick = i
			continue
		}
		less, err := s.less(group[i], group[pick])
		if err != nil {
			return 0, err
		}
		if less {
			pick = i
		}
	}
	return pick, nil
}

func (s *siblingOrder) less(a, b int) (bool, error) {
	c, err := orderCompare(s.key[a], s.key[b])
	if err != nil {
		return false, err
	}
	if c == 0 {
		c = int(s.p.Clusters[a].Decl) - int(s.p.Clusters[b].Decl)
	}
	return c < 0, nil
}

func (s *siblingOrder) level(nodes []int32, depth int) []int32 {
	items := s.items(nodes, depth)
	var slots []int
	var blocks []siblingItem
	for i, item := range items {
		if item.child == noPosition {
			continue
		}
		item.nodes = s.level(item.nodes, depth+1)
		slots = append(slots, i)
		blocks = append(blocks, item)
	}
	slices.SortStableFunc(blocks, func(a, b siblingItem) int { return s.number[a.child] - s.number[b.child] })
	for k, slot := range slots {
		items[slot] = blocks[k]
	}
	out := make([]int32, 0, len(nodes))
	for _, item := range items {
		out = append(out, item.nodes...)
	}
	return out
}

func (s *siblingOrder) items(nodes []int32, depth int) []siblingItem {
	var items []siblingItem
	for _, v := range nodes {
		child := noPosition
		if chain := s.chains[v]; len(chain) > depth {
			child = chain[depth]
		}
		last := len(items) - 1
		if child == noPosition || last < 0 || items[last].child != child {
			items = append(items, siblingItem{child: child})
			last++
		}
		items[last].nodes = append(items[last].nodes, v)
	}
	return items
}
