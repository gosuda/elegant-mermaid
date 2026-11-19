package layered

func attachmentEntry(g *Graph, candidate int) []bool {
	if len(g.Attachments) == 0 || candidate != 2 {
		return make([]bool, len(g.Edges))
	}
	return groupGreedyFlags(g)
}

func edgeFlags(g *Graph) []bool {
	flags := make([]bool, len(g.Edges))
	for i, e := range g.Edges {
		flags[i] = e.Reversed
	}
	return flags
}

func breakAttachedCycles(g *Graph) error {
	if !protectedGraph(g) {
		_, err := BreakCycles(g)
		return err
	}
	_, err := protectedCycles(g, edgeFlags(g))
	return err
}

type groupGreedy struct {
	decls []int32
	node  []int
	edges [][2]int
}

func newGroupGreedy(g *Graph) groupGreedy {
	shape := groupGreedy{node: make([]int, len(g.Nodes))}
	for i, n := range g.Nodes {
		if n.Border == BorderNone {
			shape.node[i] = len(shape.decls)
			shape.decls = append(shape.decls, n.Decl)
		}
	}
	for _, c := range g.Clusters {
		shape.node[c.Top] = len(shape.decls)
		shape.node[c.Bottom] = len(shape.decls)
		shape.decls = append(shape.decls, c.Decl)
	}
	for _, e := range g.Edges {
		if !e.Synthetic {
			shape.edges = append(shape.edges, [2]int{shape.node[e.Tail], shape.node[e.Head]})
		}
	}
	return shape
}

func groupGreedyFlags(g *Graph) []bool {
	shape := newGroupGreedy(g)
	position := shape.positions()
	flags := make([]bool, len(g.Edges))
	for i, e := range g.Edges {
		flags[i] = !e.Synthetic && position[shape.node[e.Tail]] > position[shape.node[e.Head]]
	}
	return flags
}

func (s groupGreedy) positions() []int {
	alive := make([]bool, len(s.decls))
	for i := range alive {
		alive[i] = true
	}
	var left, right []int
	for range s.decls {
		in, out := s.degrees(alive)
		v, sink := s.pick(alive, in, out)
		alive[v] = false
		if sink {
			right = append(right, v)
		} else {
			left = append(left, v)
		}
	}
	for i := len(right) - 1; i >= 0; i-- {
		left = append(left, right[i])
	}
	position := make([]int, len(s.decls))
	for i, v := range left {
		position[v] = i
	}
	return position
}

func (s groupGreedy) degrees(alive []bool) ([]int, []int) {
	in, out := make([]int, len(s.decls)), make([]int, len(s.decls))
	for _, e := range s.edges {
		if e[0] != e[1] && alive[e[0]] && alive[e[1]] {
			out[e[0]]++
			in[e[1]]++
		}
	}
	return in, out
}

func (s groupGreedy) pick(alive []bool, in, out []int) (int, bool) {
	if v := s.earliest(alive, out); v >= 0 {
		return v, true
	}
	if v := s.earliest(alive, in); v >= 0 {
		return v, false
	}
	best := -1
	for v, on := range alive {
		if on && (best < 0 || in[v]-out[v] < in[best]-out[best] || in[v]-out[v] == in[best]-out[best] && s.decls[v] < s.decls[best]) {
			best = v
		}
	}
	return best, false
}

func (s groupGreedy) earliest(alive []bool, degree []int) int {
	best := -1
	for v, on := range alive {
		if on && degree[v] == 0 && (best < 0 || s.decls[v] < s.decls[best]) {
			best = v
		}
	}
	return best
}
