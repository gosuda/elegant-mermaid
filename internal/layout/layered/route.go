package layered

import (
	"cmp"
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type RoutingSegment struct {
	Tail, Head, Decl, Slot int32
	SourceX, TargetX       int32
	Edges                  []int32
	Order                  int32
}
type RoutingGap struct {
	Segments []RoutingSegment
	Slots    int32
}
type Routing struct {
	Gaps              []RoutingGap
	SourceX, TargetX  []int32
	Segment           []int32
	Reversed          []ReversedRun
	SourceRunX        []int32
	ClusterBounds     []horizontalSpan
	LabelReservations []LabelReservation
}
type EdgeRoute struct {
	Original int32
	ID       string
	Points   []geom.Point
}
type Box struct {
	ID   string
	Rect geom.Rect
	Role scene.BoxRole
}
type routeGeometry struct {
	p                  *Proper
	r                  *Routing
	x, y, top, heights []int32
	layers             [][]int32
	slot               int32
}

func portNeighbours(p *Proper, v int32, edges []int32, x []int32) []int32 {
	ns := make([]int32, 0, len(edges))
	for _, i := range edges {
		e := p.Edges[i]
		w := e.Tail
		if w == v {
			w = e.Head
		}
		if !slices.Contains(ns, w) {
			ns = append(ns, w)
		}
	}
	slices.SortStableFunc(ns, func(a, b int32) int {
		if d := cmp.Compare(x[a], x[b]); d != 0 {
			return d
		}
		if d := cmp.Compare(p.Nodes[a].Decl, p.Nodes[b].Decl); d != 0 {
			return d
		}
		return cmp.Compare(a, b)
	})
	return ns
}

func assignPorts(p *Proper, v int32, edges []int32, x, out []int32) error {
	ns := portNeighbours(p, v, edges, x)
	w := int64(p.Nodes[v].W)
	left := int64(x[v]) - w/2
	for _, i := range edges {
		e := p.Edges[i]
		other := e.Tail
		if other == v {
			other = e.Head
		}
		j := slices.Index(ns, other)
		a := left + int64(j+1)*w/int64(len(ns)+1)
		if p.Nodes[v].Label != nil {
			a = left
		}
		if a < math.MinInt32 || a > math.MaxInt32 {
			return geom.ErrOverflow
		}
		out[i] = int32(a)
	}
	return nil
}

func routingPorts(p *Proper, x []int32, r *Routing) error {
	incoming, outgoing := make([][]int32, len(p.Nodes)), make([][]int32, len(p.Nodes))
	for i, e := range p.Edges {
		if e.Original < 0 {
			continue
		}
		incoming[e.Head] = append(incoming[e.Head], int32(i))
		outgoing[e.Tail] = append(outgoing[e.Tail], int32(i))
	}
	for v := range p.Nodes {
		if err := assignPorts(p, int32(v), outgoing[v], x, r.SourceX); err != nil {
			return err
		}
		if err := assignPorts(p, int32(v), incoming[v], x, r.TargetX); err != nil {
			return err
		}
	}
	return nil
}

func addRoutingSegment(p *Proper, r *Routing, i int) {
	e := p.Edges[i]
	gap := &r.Gaps[p.Rank[e.Tail]]
	for j := range gap.Segments {
		s := &gap.Segments[j]
		if s.Tail == e.Tail && s.Head == e.Head {
			s.Edges = append(s.Edges, int32(i))
			s.Decl = min(s.Decl, e.Decl)
			r.Segment[i] = int32(j)
			return
		}
	}
	r.Segment[i] = int32(len(gap.Segments))
	gap.Segments = append(gap.Segments, RoutingSegment{Tail: e.Tail, Head: e.Head, Decl: e.Decl, Slot: -1, SourceX: r.sourceRun(i), TargetX: r.TargetX[i], Edges: []int32{int32(i)}})
}

func routingConflict(a, b RoutingSegment) bool {
	if a.SourceX == a.TargetX || b.SourceX == b.TargetX {
		return false
	}
	return max(min(a.SourceX, a.TargetX), min(b.SourceX, b.TargetX)) <= min(max(a.SourceX, a.TargetX), max(b.SourceX, b.TargetX))
}

func directionClass(s RoutingSegment) int {
	if s.TargetX > s.SourceX {
		return 1
	}
	return 0
}

func segmentOrder(a, b RoutingSegment) int {
	class := cmp.Compare(directionClass(a), directionClass(b))
	if class != 0 {
		return class
	}
	source := cmp.Compare(a.SourceX, b.SourceX)
	if directionClass(a) == 1 {
		source = -source
	}
	return cmp.Or(source, cmp.Compare(a.Decl, b.Decl), cmp.Compare(a.Order, b.Order))
}

func numberRoutingGap(gap *RoutingGap) {
	n := len(gap.Segments)
	incoming := make([]int, n)
	out := make([][]int, n)
	done := make([]bool, n)
	for i, a := range gap.Segments {
		for j, b := range gap.Segments {
			if segmentOrder(a, b) < 0 && routingConflict(a, b) {
				out[i] = append(out[i], j)
				incoming[j]++
			}
		}
	}
	for range n {
		v := readySegment(gap, incoming, done)
		if v < 0 {
			return
		}
		done[v] = true
		s := &gap.Segments[v]
		if s.SourceX != s.TargetX {
			s.Slot = max(s.Slot, 0)
			gap.Slots = max(gap.Slots, s.Slot+1)
		}
		for _, w := range out[v] {
			incoming[w]--
			gap.Segments[w].Slot = max(gap.Segments[w].Slot, s.Slot+1)
		}
	}
}

func readySegment(gap *RoutingGap, incoming []int, done []bool) int {
	v := -1
	for i, s := range gap.Segments {
		if done[i] || incoming[i] != 0 {
			continue
		}
		if v < 0 || s.Decl < gap.Segments[v].Decl {
			v = i
		}
	}
	return v
}

func Route(p *Proper, layers [][]int32, x []int32) (*Routing, error) {
	if _, err := coordinateLayers(p, layers); err != nil {
		return nil, err
	}
	if len(x) != len(p.Nodes) {
		return nil, ErrGraph
	}
	if _, err := coordinateParams(p); err != nil {
		return nil, err
	}
	r := &Routing{Gaps: make([]RoutingGap, max(0, len(layers)-1)), SourceX: make([]int32, len(p.Edges)), TargetX: make([]int32, len(p.Edges)), Segment: make([]int32, len(p.Edges))}
	if err := routingPorts(p, x, r); err != nil {
		return nil, err
	}
	if err := groupProxyPorts(p, x, r); err != nil {
		return nil, err
	}
	for i := range p.Edges {
		if !drawChain(p, p.Edges[i]) {
			continue
		}
		addRoutingSegment(p, r, i)
	}
	if err := reversedRuns(p, x, r); err != nil {
		return nil, err
	}
	for i := range r.Gaps {
		numberRoutingGap(&r.Gaps[i])
	}
	return r, nil
}

func (g routeGeometry) chainPoints(e ProperEdge, i int, slot int32) ([]geom.Point, error) {
	p, r, y, top, h := g.p, g.r, g.y, g.top, g.heights
	a := geom.Point{X: r.SourceX[i], Y: y[e.Tail]}
	n := int64(a.Y) + int64(p.Nodes[e.Tail].H)
	snapped := sourceTopProxy(p, e)
	if snapped {
		n = int64(top[p.Rank[e.Tail]])
	}
	if n > math.MaxInt32 {
		return nil, geom.ErrOverflow
	}
	a.Y = int32(n)
	b := geom.Point{X: r.TargetX[i], Y: y[e.Head]}
	var run int32
	if snapped {
		run = r.sourceRun(i)
	} else {
		run = gutterRun(p, r, e.Tail, int32(i))
	}
	points := appendRoutePoints(nil, []geom.Point{a, {X: run, Y: a.Y}})
	if run == b.X {
		return appendRoutePoints(points, []geom.Point{b}), nil
	}
	rank := p.Rank[e.Tail]
	s := r.Gaps[rank].Segments[r.Segment[i]]
	mid := int64(top[rank]) + int64(h[rank]) + int64(slot)*(int64(s.Slot)+1) + int64(slot)/2
	if mid > math.MaxInt32 {
		return nil, geom.ErrOverflow
	}
	return appendRoutePoints(points, []geom.Point{{X: run, Y: int32(mid)}, {X: b.X, Y: int32(mid)}, b}), nil
}

func RoutePoints(p *Proper, layers [][]int32, x, y, rankTop []int32, r *Routing) ([]EdgeRoute, []Box, error) {
	geometry := routeGeometry{p: p, r: r, x: x, y: y, top: rankTop, layers: layers}
	if err := geometry.prepare(); err != nil {
		return nil, nil, err
	}
	return geometry.points()
}

func (g *routeGeometry) prepare() error {
	if _, err := coordinateLayers(g.p, g.layers); err != nil {
		return err
	}
	if len(g.x) != len(g.p.Nodes) || len(g.y) != len(g.p.Nodes) || len(g.top) != len(g.layers) || g.r == nil {
		return ErrGraph
	}
	params, err := coordinateParams(g.p)
	if err != nil {
		return err
	}
	g.slot = params.Slot
	g.heights = rankHeights(g.p, g.layers)
	return nil
}

func (g routeGeometry) points() ([]EdgeRoute, []Box, error) {
	routes, err := g.chains()
	if err != nil {
		return nil, nil, err
	}
	labels, err := placedLabels(g.p, g.x, g.y)
	if err != nil {
		return nil, nil, err
	}
	if err := g.reversedPoints(routes, &labels); err != nil {
		return nil, nil, err
	}
	g.r.LabelReservations = labels.reservations
	return routes, labels.boxes, nil
}

func (g routeGeometry) chains() ([]EdgeRoute, error) {
	routes := make([]EdgeRoute, len(g.p.Chains))
	for i := range routes {
		routes[i].Original = int32(i)
	}
	for i, e := range g.p.Edges {
		if !drawChain(g.p, e) {
			continue
		}
		points, err := g.chainPoints(e, i, g.slot)
		if err != nil {
			return nil, err
		}
		routes[e.Original].Points = appendRoutePoints(routes[e.Original].Points, points)
	}
	return routes, nil
}

func appendRoutePoints(out, points []geom.Point) []geom.Point {
	for _, point := range points {
		if len(out) == 0 || out[len(out)-1] != point {
			out = append(out, point)
		}
	}
	return out
}

func (r *Routing) sourceRun(index int) int32 {
	if len(r.SourceRunX) > 0 {
		return r.SourceRunX[index]
	}
	return r.SourceX[index]
}

func sizeProperPorts(g *Graph, p *Proper) error {
	for i, node := range g.Nodes {
		if node.Border != BorderNone || node.Role == scene.RoleGroup || node.Exact {
			continue
		}
		count := max(properNeighbourCount(p, int32(i), p.In[i]), properNeighbourCount(p, int32(i), p.Out[i]))
		width, err := coordinate((int64(count) + 1) * int64(g.PortGap))
		if err != nil {
			return err
		}
		g.Nodes[i].W = max(g.Nodes[i].W, width)
		p.Nodes[i].W = g.Nodes[i].W
	}
	return nil
}

func properNeighbourCount(p *Proper, node int32, edges []int32) int {
	neighbours := make(map[int32]struct{}, len(edges))
	for _, index := range edges {
		edge := p.Edges[index]
		if edge.Original < 0 {
			continue
		}
		neighbour := edge.Tail
		if neighbour == node {
			neighbour = edge.Head
		}
		neighbours[neighbour] = struct{}{}
	}
	return len(neighbours)
}
