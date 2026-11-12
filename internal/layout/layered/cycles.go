package layered

const (
	unvisited uint8 = iota
	onStack
	finished
)

type dfsFrame struct {
	node int32
	next int
}

func BreakCycles(g *Graph) ([]bool, error) {
	if err := validateGraph(g); err != nil {
		return nil, err
	}
	for i := range g.Edges {
		g.Edges[i].Reversed = false
	}
	reversed := make([]bool, len(g.Edges))
	state := make([]uint8, len(g.Nodes))
	out := declaredOut(g)
	stack := make([]dfsFrame, 0, len(g.Nodes))
	for start := range g.Nodes {
		if state[start] != unvisited {
			continue
		}
		state[start] = onStack
		stack = append(stack, dfsFrame{node: int32(start)})
		stack = drainSearch(g, out, state, reversed, stack)
	}
	g.RebuildAdjacency()
	return reversed, nil
}

func drainSearch(g *Graph, out [][]int32, state []uint8, reversed []bool, stack []dfsFrame) []dfsFrame {
	for len(stack) > 0 {
		top := &stack[len(stack)-1]
		edges := out[top.node]
		if top.next >= len(edges) {
			state[top.node] = finished
			stack = stack[:len(stack)-1]
			continue
		}
		index := edges[top.next]
		top.next++
		edge := &g.Edges[index]
		if edge.SelfLoop() {
			continue
		}
		switch state[edge.Head] {
		case onStack:
			edge.Reversed = true
			reversed[index] = true
		case unvisited:
			state[edge.Head] = onStack
			stack = append(stack, dfsFrame{node: edge.Head})
		}
	}
	return stack
}
