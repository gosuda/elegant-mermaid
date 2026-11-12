package layered

import (
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func Portfolio(g *Graph, thoroughness int) (Layout, error) {
	if err := validateGraph(g); err != nil {
		return Layout{}, err
	}
	if thoroughness == 0 {
		thoroughness = 3
	}
	if thoroughness < 1 || thoroughness > 5 {
		return Layout{}, ErrGraph
	}
	choice, err := initialPortfolio(g)
	if err != nil {
		return Layout{}, err
	}
	for candidate := 1; candidate < thoroughness; candidate++ {
		if err := choice.consider(g, candidate); err != nil {
			return Layout{}, err
		}
	}
	choice.layout.BudgetExhausted = choice.budget
	return choice.layout, nil
}

type portfolioChoice struct {
	layout Layout
	cost   int64
	budget bool
}

func initialPortfolio(g *Graph) (portfolioChoice, error) {
	layout, err := candidateLayout(g, 0)
	if err != nil {
		return portfolioChoice{}, err
	}
	cost, err := softCost(g, layout)
	if err != nil {
		return portfolioChoice{}, err
	}
	return portfolioChoice{layout: layout, cost: cost, budget: layout.BudgetExhausted}, nil
}
func (choice *portfolioChoice) consider(g *Graph, candidate int) error {
	trial, err := candidateLayout(g, candidate)
	if err != nil {
		return err
	}
	cost, err := softCost(g, trial)
	if err != nil {
		return err
	}
	improves, err := portfolioImproves(choice.cost, cost)
	if err != nil {
		return err
	}
	choice.budget = choice.budget || trial.BudgetExhausted
	if improves {
		choice.layout = trial
		choice.cost = cost
	}
	return nil
}
func portfolioImproves(incumbent, candidate int64) (bool, error) {
	lhs, err := product(candidate, 100)
	if err != nil {
		return false, err
	}
	rhs, err := product(incumbent, 97)
	if err != nil {
		return false, err
	}
	return lhs < rhs, nil
}
func candidateLayout(g *Graph, candidate int) (Layout, error) {
	graph := cloneGraph(g)
	if err := candidateCycles(graph, candidate); err != nil {
		return Layout{}, err
	}
	options := OrderOptions{}
	switch candidate {
	case 1:
		options.Start = OrderStartBreadthFirst
	case 3:
		options.Key = OrderKeyMedian
	case 4:
		options.Start = OrderStartReverse
	}
	return runComponent(graph, options)
}
func candidateCycles(g *Graph, candidate int) error {
	if candidate != 2 {
		_, err := BreakCycles(g)
		return err
	}
	greedyCycles(g)
	if !protectedGraph(g) {
		return nil
	}
	preferred := make([]bool, len(g.Edges))
	for i, e := range g.Edges {
		preferred[i] = e.Reversed
	}
	_, err := protectedCycles(g, preferred)
	return err
}
func greedyCycles(g *Graph) {
	remaining := make([]bool, len(g.Nodes))
	for i := range remaining {
		remaining[i] = true
	}
	var left, right []int32
	for range g.Nodes {
		v, kind := feedbackVertex(g, remaining)
		remaining[v] = false
		if kind < 0 {
			right = append(right, v)
		} else {
			left = append(left, v)
		}
	}
	slices.Reverse(right)
	left = append(left, right...)
	pos := make([]int, len(g.Nodes))
	for i, v := range left {
		pos[v] = i
	}
	for i, e := range g.Edges {
		g.Edges[i].Reversed = !e.Synthetic && !e.SelfLoop() && pos[e.Tail] > pos[e.Head]
	}
	g.RebuildAdjacency()
}
func feedbackVertex(g *Graph, remaining []bool) (int32, int) {
	in, out := make([]int, len(g.Nodes)), make([]int, len(g.Nodes))
	for _, e := range g.Edges {
		if !e.SelfLoop() && remaining[e.Tail] && remaining[e.Head] {
			out[e.Tail]++
			in[e.Head]++
		}
	}
	if sink := feedbackEndpoint(g, remaining, out); sink >= 0 {
		return sink, -1
	}
	if source := feedbackEndpoint(g, remaining, in); source >= 0 {
		return source, 1
	}
	return feedbackMaximum(g, remaining, in, out), 0
}
func feedbackEndpoint(g *Graph, remaining []bool, degree []int) int32 {
	best := int32(-1)
	for v, on := range remaining {
		if on && degree[v] == 0 && earlierNode(g, int32(v), best) {
			best = int32(v)
		}
	}
	return best
}
func feedbackMaximum(g *Graph, remaining []bool, in, out []int) int32 {
	best := int32(-1)
	for v, on := range remaining {
		if !on {
			continue
		}
		if feedbackPreferred(g, int32(v), best, in, out) {
			best = int32(v)
		}
	}
	return best
}
func feedbackPreferred(g *Graph, a, b int32, in, out []int) bool {
	if b < 0 {
		return true
	}
	deltaA, deltaB := out[a]-in[a], out[b]-in[b]
	if deltaA != deltaB {
		return deltaA > deltaB
	}
	return earlierNode(g, a, b)
}
func earlierNode(g *Graph, a, b int32) bool {
	return b < 0 || g.Nodes[a].Decl < g.Nodes[b].Decl || g.Nodes[a].Decl == g.Nodes[b].Decl && a < b
}
func product(a, b int64) (int64, error) {
	if a == 0 || b == 0 {
		return 0, nil
	}
	bound := uint64(math.MaxInt64)
	if (a < 0) != (b < 0) {
		bound = uint64(1) << 63
	}
	if magnitude(a) > bound/magnitude(b) {
		return 0, geom.ErrOverflow
	}
	return a * b, nil
}
func magnitude(n int64) uint64 {
	if n < 0 {
		return uint64(-(n + 1)) + 1
	}
	return uint64(n)
}
func softCost(g *Graph, part Layout) (int64, error) {
	var sum, n int64
	for _, b := range part.Boxes {
		if b.Role != scene.RoleNode {
			continue
		}
		sum += (int64(b.Rect.W) + int64(b.Rect.H)) / 2
		n++
	}
	mean := max(int64(1), sum/max(int64(1), n))
	stats, err := routeCost(g, part)
	if err != nil {
		return 0, err
	}
	part.Extents = nil
	b, err := layoutBounds(part)
	if err != nil {
		return 0, err
	}
	area := int64(b.W) * int64(b.H)
	return (scene.Metrics{
		Nodes: n, MeanNodeExtent: mean, Crossings: stats.crossings,
		Bends: stats.bends, AgainstFlowEdges: stats.against,
		TotalRouteLength: stats.length, CanvasArea: area,
	}).Cost()
}

type routeStats struct{ crossings, bends, against, length int64 }

func routeCost(g *Graph, part Layout) (routeStats, error) {
	var out routeStats
	for i, r := range part.Routes {
		points := appendRoutePoints(nil, r.Points)
		length, bends, err := pathCost(points)
		if err != nil {
			return out, err
		}
		out.length += length
		out.bends += bends
		out.against += againstFlow(g, part, r)
		for j := 0; j < i; j++ {
			count, err := routeCrossings(points, part.Routes[j].Points)
			if err != nil {
				return out, err
			}
			out.crossings += count
		}
	}
	return out, nil
}
func againstFlow(g *Graph, part Layout, r EdgeRoute) int64 {
	from, to, ok := routeEndpoints(g, r)
	if !ok || from == to {
		return 0
	}
	a, b := findBox(part.Boxes, from), findBox(part.Boxes, to)
	if 2*int64(b.Y)+int64(b.H) < 2*int64(a.Y)+int64(a.H) {
		return 1
	}
	return 0
}
func routeEndpoints(g *Graph, r EdgeRoute) (string, string, bool) {
	for _, e := range g.Edges {
		if e.Synthetic || !sameRoute(e, r) {
			continue
		}
		from, to := edgeEndpointIDs(g, e)
		return from, to, true
	}
	for _, f := range g.Fixed {
		for _, edge := range f.Scene.Routes {
			if edge.ID == r.ID {
				return edge.From, edge.To, true
			}
		}
	}
	return "", "", false
}

func edgeEndpointIDs(g *Graph, e Edge) (string, string) {
	from, to := g.Nodes[e.Tail].ID, g.Nodes[e.Head].ID
	if e.SourceGroup != "" {
		from = e.SourceGroup
	}
	if e.TargetGroup != "" {
		to = e.TargetGroup
	}
	if e.FrameLoop != "" {
		from = e.FrameLoop
		to = e.FrameLoop
	}
	return from, to
}
func sameRoute(e Edge, r EdgeRoute) bool {
	if r.ID != "" {
		return e.ID == r.ID
	}
	return e.Decl == r.Original
}
func findBox(boxes []Box, id string) geom.Rect {
	for _, b := range boxes {
		if b.ID == id {
			return b.Rect
		}
	}
	return geom.Rect{}
}
func pathCost(points []geom.Point) (int64, int64, error) {
	var length, bends int64
	for i := 1; i < len(points); i++ {
		step, err := segmentLength(points[i-1], points[i])
		if err != nil {
			return 0, 0, err
		}
		if length > math.MaxInt64-step {
			return 0, 0, geom.ErrOverflow
		}
		length += step
		if i > 1 {
			bend, err := isBend(points[i-2], points[i-1], points[i])
			if err != nil {
				return 0, 0, err
			}
			if bend {
				bends++
			}
		}
	}
	return length, bends, nil
}

func segmentLength(a, b geom.Point) (int64, error) {
	dx, dy := int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y)
	xx, err := product(dx, dx)
	if err != nil {
		return 0, err
	}
	yy, err := product(dy, dy)
	if err != nil {
		return 0, err
	}
	if xx > math.MaxInt64-yy {
		return 0, geom.ErrOverflow
	}
	return geom.Isqrt(xx + yy)
}
func determinant(a, b, c, d int64) (int64, error) {
	x, err := product(a, d)
	if err != nil {
		return 0, err
	}
	y, err := product(b, c)
	if err != nil {
		return 0, err
	}
	arithmetic := coordinateArithmetic{}
	n := arithmetic.subtract(x, y)
	return n, arithmetic.err
}
func isBend(a, b, c geom.Point) (bool, error) {
	dx, dy := int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y)
	ex, ey := int64(c.X)-int64(b.X), int64(c.Y)-int64(b.Y)
	cross, err := determinant(dx, dy, ex, ey)
	if err != nil {
		return false, err
	}
	if cross != 0 {
		return true, nil
	}
	x, err := product(dx, ex)
	if err != nil {
		return false, err
	}
	y, err := product(dy, ey)
	if err != nil {
		return false, err
	}
	arithmetic := coordinateArithmetic{}
	dot := arithmetic.add(x, y)
	return dot < 0, arithmetic.err
}
func orientation(a, b, c geom.Point) (int64, error) {
	n, err := determinant(int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y), int64(c.X)-int64(a.X), int64(c.Y)-int64(a.Y))
	if n < 0 {
		return -1, err
	}
	if n > 0 {
		return 1, err
	}
	return 0, err
}
func segmentsCross(a, b, c, d geom.Point) (bool, error) {
	x, err := orientation(a, b, c)
	if err != nil {
		return false, err
	}
	y, err := orientation(a, b, d)
	if err != nil {
		return false, err
	}
	z, err := orientation(c, d, a)
	if err != nil {
		return false, err
	}
	w, err := orientation(c, d, b)
	if err != nil {
		return false, err
	}
	return x*y == -1 && z*w == -1, nil
}
func routeCrossings(a, b []geom.Point) (int64, error) {
	var count int64
	for i := 1; i < len(a); i++ {
		for j := 1; j < len(b); j++ {
			cross, err := segmentsCross(a[i-1], a[i], b[j-1], b[j])
			if err != nil {
				return 0, err
			}
			if cross {
				count++
			}
		}
	}
	return count, nil
}
