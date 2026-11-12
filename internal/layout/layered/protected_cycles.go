package layered

type reachability struct {
	out        [][]int32
	seen       []uint32
	generation uint32
	queue      []int32
}

func protectedGraph(g *Graph) bool {
	for _, e := range g.Edges {
		if e.Synthetic {
			return true
		}
	}
	return false
}
func protectedCycles(g *Graph, preferred []bool) ([]bool, error) {
	search := reachability{out: make([][]int32, len(g.Nodes)), seen: make([]uint32, len(g.Nodes)), queue: make([]int32, 0, len(g.Nodes))}
	reversed := make([]bool, len(g.Edges))
	for i := range g.Edges {
		g.Edges[i].Reversed = false
	}
	if err := search.constraints(g); err != nil {
		return nil, err
	}
	for i, e := range g.Edges {
		if e.Synthetic || e.SelfLoop() {
			continue
		}
		if i < len(preferred) {
			e.Reversed = preferred[i]
		}
		reversed[i] = search.insert(e)
		g.Edges[i].Reversed = reversed[i]
	}
	g.RebuildAdjacency()
	return reversed, nil
}
func (r *reachability) constraints(g *Graph) error {
	for _, e := range g.Edges {
		if !e.Synthetic {
			continue
		}
		if r.path(e.Head, e.Tail) {
			return ErrCycle
		}
		r.out[e.Tail] = append(r.out[e.Tail], e.Head)
	}
	return nil
}
func (r *reachability) insert(e Edge) bool {
	a, b := e.Chain()
	reversed := e.Reversed
	if r.path(b, a) {
		a, b = b, a
		reversed = !reversed
	}
	r.out[a] = append(r.out[a], b)
	return reversed
}
func (r *reachability) path(from, to int32) bool {
	r.generation++
	r.queue = r.queue[:0]
	r.queue = append(r.queue, from)
	r.seen[from] = r.generation
	for at := 0; at < len(r.queue); at++ {
		v := r.queue[at]
		if v == to {
			return true
		}
		r.enqueue(v)
	}
	return false
}
func (r *reachability) enqueue(v int32) {
	for _, w := range r.out[v] {
		if r.seen[w] == r.generation {
			continue
		}
		r.seen[w] = r.generation
		r.queue = append(r.queue, w)
	}
}
