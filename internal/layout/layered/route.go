package layered

import (
	"cmp"
	"math"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type RoutingSegment struct {
	Tail, Head, Decl, Slot int32
	SourceX, TargetX       int32
	Edges                  []int32
}
type RoutingGap struct {
	Segments []RoutingSegment
	Slots    int32
}
type Routing struct {
	Gaps             []RoutingGap
	SourceX, TargetX []int32
	Segment          []int32
}
type EdgeRoute struct {
	Original int32
	Points   []geom.Point
}
type Box struct {
	ID   string
	Rect geom.Rect
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
	gap.Segments = append(gap.Segments, RoutingSegment{Tail: e.Tail, Head: e.Head, Decl: e.Decl, Slot: -1, SourceX: r.SourceX[i], TargetX: r.TargetX[i], Edges: []int32{int32(i)}})
}
func routingConflict(a, b RoutingSegment) bool {
	if a.SourceX == a.TargetX || b.SourceX == b.TargetX {
		return false
	}
	return max(min(a.SourceX, a.TargetX), min(b.SourceX, b.TargetX)) <= min(max(a.SourceX, a.TargetX), max(b.SourceX, b.TargetX))
}
func segmentOrder(a, b RoutingSegment) int {
	if d := cmp.Compare(a.SourceX, b.SourceX); d != 0 {
		return d
	}
	return cmp.Compare(a.Decl, b.Decl)
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
	for i := range p.Edges {
		addRoutingSegment(p, r, i)
	}
	for i := range r.Gaps {
		numberRoutingGap(&r.Gaps[i])
	}
	return r, nil
}
func chainPoints(p *Proper, e ProperEdge, i int, y, top, h []int32, r *Routing, slot int32) ([]geom.Point, error) {
	a := geom.Point{X: r.SourceX[i], Y: y[e.Tail]}
	n := int64(a.Y) + int64(p.Nodes[e.Tail].H)
	if n > math.MaxInt32 {
		return nil, geom.ErrOverflow
	}
	a.Y = int32(n)
	b := geom.Point{X: r.TargetX[i], Y: y[e.Head]}
	if a.X == b.X {
		return []geom.Point{a, b}, nil
	}
	rank := p.Rank[e.Tail]
	s := r.Gaps[rank].Segments[r.Segment[i]]
	mid := int64(top[rank]) + int64(h[rank]) + int64(slot)*(int64(s.Slot)+1) + int64(slot)/2
	if mid > math.MaxInt32 {
		return nil, geom.ErrOverflow
	}
	return []geom.Point{a, {X: a.X, Y: int32(mid)}, {X: b.X, Y: int32(mid)}, b}, nil
}
func RoutePoints(p *Proper, layers [][]int32, x, y, rankTop []int32, r *Routing) ([]EdgeRoute, []Box, error) {
	if _, err := coordinateLayers(p, layers); err != nil {
		return nil, nil, err
	}
	if len(x) != len(p.Nodes) || len(y) != len(p.Nodes) || len(rankTop) != len(layers) || r == nil {
		return nil, nil, ErrGraph
	}
	params, err := coordinateParams(p)
	if err != nil {
		return nil, nil, err
	}
	h := rankHeights(p, layers)
	routes := make([]EdgeRoute, len(p.Chains))
	for i := range routes {
		routes[i].Original = int32(i)
	}
	for i, e := range p.Edges {
		points, err := chainPoints(p, e, i, y, rankTop, h, r, params.Slot)
		if err != nil {
			return nil, nil, err
		}
		route := &routes[e.Original]
		route.Points = appendRoutePoints(route.Points, points)
	}
	return routes, []Box{}, nil
}
func appendRoutePoints(out, points []geom.Point) []geom.Point {
	for _, point := range points {
		if len(out) == 0 || out[len(out)-1] != point {
			out = append(out, point)
		}
	}
	return out
}
