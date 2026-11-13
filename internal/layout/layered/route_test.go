package layered

import (
	"cmp"
	"fmt"
	"reflect"
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type routedCase struct {
	p         *Proper
	layers    [][]int32
	x, y, top []int32
	r         *Routing
	routes    []EdgeRoute
}

func routeCase(t *testing.T, p *Proper, layers [][]int32) routedCase {
	t.Helper()
	x, err := CrossCoords(p, layers)
	if err != nil {
		t.Fatal(err)
	}
	return routeWith(t, p, layers, x, nil)
}
func routeWith(t *testing.T, p *Proper, layers [][]int32, x []int32, renumber func(*RoutingGap)) routedCase {
	t.Helper()
	r, err := Route(p, layers, x)
	if err != nil {
		t.Fatal(err)
	}
	for i := range r.Gaps {
		if renumber != nil {
			renumber(&r.Gaps[i])
		}
	}
	y, top, err := RankCoords(p, layers, r)
	if err != nil {
		t.Fatal(err)
	}
	routes, _, err := RoutePoints(p, layers, x, y, top, r)
	if err != nil {
		t.Fatal(err)
	}
	return routedCase{p, layers, x, y, top, r, routes}
}
func TestRoutingRandom(t *testing.T) {
	for i := range 200 {
		t.Run(fmt.Sprint(i), func(t *testing.T) {
			p, l := coordinateCase(t, i)
			c := routeCase(t, p, l)
			checkBands(t, c)
			checkSlots(t, c)
			for _, route := range c.routes {
				checkRoute(t, c, route)
			}
			if i < 5 {
				t.Logf("case=%d x=%v y=%v rankTop=%v routes=%v", i, c.x, c.y, c.top, c.routes)
			}
		})
	}
}
func checkBands(t *testing.T, c routedCase) {
	t.Helper()
	h := rankHeights(c.p, c.layers)
	for i := 1; i < len(h); i++ {
		if c.top[i] < c.top[i-1]+h[i-1] {
			t.Fatal("overlapping rank bands")
		}
	}
}
func checkSlots(t *testing.T, c routedCase) {
	t.Helper()
	for _, gap := range c.r.Gaps {
		for i, a := range gap.Segments {
			for _, b := range gap.Segments[i+1:] {
				if routingConflict(a, b) && a.Slot == b.Slot {
					t.Fatalf("overlapping slots: %v %v", a, b)
				}
			}
		}
	}
}
func checkRoute(t *testing.T, c routedCase, r EdgeRoute) {
	t.Helper()
	if !geom.IsOrthogonal(r.Points) {
		t.Fatal("diagonal route", r)
	}
	chain := c.p.Chains[r.Original]
	a, b := chain[0], chain[len(chain)-1]
	first, last := r.Points[0], r.Points[len(r.Points)-1]
	if first.Y != c.y[a]+c.p.Nodes[a].H || last.Y != c.y[b] {
		t.Fatal("wrong port side", r)
	}
	for v, n := range c.p.Nodes {
		if n.Dummy || int32(v) == a || int32(v) == b {
			continue
		}
		rect := geom.Rect{X: c.x[v] - n.W/2, Y: c.y[v], W: n.W, H: n.H}
		hit, err := geom.PolylineHitsRect(r.Points, rect)
		if err != nil {
			t.Fatal(err)
		}
		if hit {
			t.Fatalf("route %v hits node %d: %v", r, v, rect)
		}
	}
}
func handProper(t *testing.T, n int, edges [][2]int32) (*Proper, [][]int32) {
	t.Helper()
	params, err := DefaultParams(scene.ProfileVector)
	if err != nil {
		t.Fatal(err)
	}
	g := &Graph{Params: params}
	for i := range n {
		g.Nodes = append(g.Nodes, Node{Decl: int32(i), W: 2048, H: 1280})
	}
	for i, e := range edges {
		g.Edges = append(g.Edges, Edge{Tail: e[0], Head: e[1], Decl: int32(i), MinLen: 1})
	}
	rank, err := Rank(g)
	if err != nil {
		t.Fatal(err)
	}
	p, err := Normalize(g, rank)
	if err != nil {
		t.Fatal(err)
	}
	var layers [][]int32
	for v, r := range p.Rank {
		for len(layers) <= int(r) {
			layers = append(layers, nil)
		}
		layers[r] = append(layers[r], int32(v))
	}
	return p, layers
}
func TestStraightRoute(t *testing.T) {
	p, l := handProper(t, 2, [][2]int32{{0, 1}})
	c := routeCase(t, p, l)
	if !reflect.DeepEqual(c.x, []int32{0, 0}) || !reflect.DeepEqual(c.y, []int32{0, 4352}) {
		t.Fatalf("x %v y %v", c.x, c.y)
	}
	want := []geom.Point{{X: 0, Y: 1280}, {X: 0, Y: 4352}}
	if !reflect.DeepEqual(c.routes[0].Points, want) {
		t.Fatal(c.routes)
	}
}
func TestDiamondPorts(t *testing.T) {
	p, l := handProper(t, 4, [][2]int32{{0, 1}, {0, 2}, {1, 3}, {2, 3}})
	c := routeCase(t, p, l)
	wantX := []int32{1792, 0, 3584, 1792}
	if !reflect.DeepEqual(c.x, wantX) {
		t.Fatalf("x %v", c.x)
	}
	wantSrc := []int32{1450, 2133, 0, 3584}
	wantTgt := []int32{0, 3584, 1450, 2133}
	if !reflect.DeepEqual(c.r.SourceX, wantSrc) || !reflect.DeepEqual(c.r.TargetX, wantTgt) {
		t.Fatalf("ports %v %v", c.r.SourceX, c.r.TargetX)
	}
	for _, g := range c.r.Gaps {
		if g.Slots != 1 {
			t.Fatal(g)
		}
	}
	wantPoints := [][]geom.Point{
		{{X: 1450, Y: 1280}, {X: 1450, Y: 2432}, {X: 0, Y: 2432}, {X: 0, Y: 5120}},
		{{X: 2133, Y: 1280}, {X: 2133, Y: 2432}, {X: 3584, Y: 2432}, {X: 3584, Y: 5120}},
		{{X: 0, Y: 6400}, {X: 0, Y: 7552}, {X: 1450, Y: 7552}, {X: 1450, Y: 10240}},
		{{X: 3584, Y: 6400}, {X: 3584, Y: 7552}, {X: 2133, Y: 7552}, {X: 2133, Y: 10240}},
	}
	for i, points := range wantPoints {
		if !reflect.DeepEqual(c.routes[i].Points, points) {
			t.Fatalf("route %d: %v", i, c.routes[i].Points)
		}
	}
}
func TestThreePorts(t *testing.T) {
	p, l := handProper(t, 4, [][2]int32{{0, 1}, {0, 2}, {0, 3}})
	x := []int32{2000, 0, 2000, 4000}
	r, err := Route(p, l, x)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(r.SourceX, []int32{1488, 2000, 2512}) {
		t.Fatal(r.SourceX)
	}
}
func slotSegment(source, target, decl, order int32) RoutingSegment {
	return RoutingSegment{Tail: -1, Head: -1, Decl: decl, Slot: -1, SourceX: source, TargetX: target, Order: order}
}
func TestSegmentOrderKey(t *testing.T) {
	cases := []struct {
		name string
		a, b RoutingSegment
	}{
		{"left-going before right-going", slotSegment(900, 100, 5, 1), slotSegment(100, 900, 0, 0)},
		{"left-going by ascending source", slotSegment(300, 0, 1, 0), slotSegment(400, 100, 0, 0)},
		{"right-going by descending source", slotSegment(400, 900, 1, 0), slotSegment(300, 800, 0, 0)},
		{"decl after equal source", slotSegment(300, 900, 0, 1), slotSegment(300, 800, 1, 0)},
		{"run after equal decl", slotSegment(300, 900, 4, 0), slotSegment(300, 800, 4, 1)},
		{"straight takes the left-going class", slotSegment(300, 300, 7, 0), slotSegment(100, 900, 0, 0)},
	}
	for _, c := range cases {
		if segmentOrder(c.a, c.b) != -1 || segmentOrder(c.b, c.a) != 1 {
			t.Errorf("%s: %d %d", c.name, segmentOrder(c.a, c.b), segmentOrder(c.b, c.a))
		}
	}
	if segmentOrder(slotSegment(1, 2, 3, 4), slotSegment(1, 2, 3, 4)) != 0 {
		t.Error("equal keys must compare equal")
	}
}
func TestNumberRoutingGapDirection(t *testing.T) {
	gap := RoutingGap{Segments: []RoutingSegment{
		slotSegment(100, 900, 3, 0),
		slotSegment(100, 900, 3, 1),
		slotSegment(700, 200, 0, 0),
		slotSegment(300, 300, 1, 0),
	}}
	numberRoutingGap(&gap)
	var slots []int32
	for _, s := range gap.Segments {
		slots = append(slots, s.Slot)
	}
	if !reflect.DeepEqual(slots, []int32{1, 2, 0, -1}) || gap.Slots != 3 {
		t.Fatalf("slots %v count %d", slots, gap.Slots)
	}
}
func routesCrossings(t *testing.T, routes []EdgeRoute) int64 {
	t.Helper()
	var total int64
	for i, a := range routes {
		for _, b := range routes[i+1:] {
			n, err := routeCrossings(a.Points, b.Points)
			if err != nil {
				t.Fatal(err)
			}
			total += n
		}
	}
	return total
}
func numberByOldKey(gap *RoutingGap) {
	order := make([]int, len(gap.Segments))
	for i := range order {
		order[i] = i
	}
	slices.SortStableFunc(order, func(i, j int) int {
		a, b := gap.Segments[i], gap.Segments[j]
		return cmp.Or(cmp.Compare(a.SourceX, b.SourceX), cmp.Compare(a.Decl, b.Decl), cmp.Compare(a.Order, b.Order))
	})
	gap.Slots = 0
	for n, i := range order {
		s := &gap.Segments[i]
		if s.SourceX == s.TargetX {
			continue
		}
		s.Slot = 0
		for _, u := range order[:n] {
			if routingConflict(gap.Segments[u], *s) {
				s.Slot = max(s.Slot, gap.Segments[u].Slot+1)
			}
		}
		gap.Slots = max(gap.Slots, s.Slot+1)
	}
}
func edgeSlots(c routedCase) []int32 {
	slots := make([]int32, len(c.p.Edges))
	for i := range slots {
		slots[i] = c.r.Gaps[c.p.Rank[c.p.Edges[i].Tail]].Segments[c.r.Segment[i]].Slot
	}
	return slots
}
func checkFan(t *testing.T, c routedCase, slots []int32, crossings int64) {
	t.Helper()
	if got := edgeSlots(c); !reflect.DeepEqual(got, slots) {
		t.Fatalf("slots %v want %v", got, slots)
	}
	if n := routesCrossings(t, c.routes); n != crossings {
		t.Fatalf("%d crossings among the routes of one fan, want %d", n, crossings)
	}
}
func TestFanSlotOrder(t *testing.T) {
	cases := []struct {
		name       string
		edges      [][2]int32
		x          []int32
		slots, old []int32
	}{
		{"fan-out", [][2]int32{{0, 1}, {0, 2}, {0, 3}, {0, 4}}, []int32{5000, 0, 2000, 8000, 10000}, []int32{0, 1, 1, 0}, []int32{0, 1, 0, 1}},
		{"fan-in", [][2]int32{{0, 4}, {1, 4}, {2, 4}, {3, 4}}, []int32{0, 2000, 8000, 10000, 5000}, []int32{1, 0, 0, 1}, []int32{0, 1, 0, 1}},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			p, l := handProper(t, 5, tc.edges)
			c := routeWith(t, p, l, tc.x, nil)
			checkFan(t, c, tc.slots, 0)
			for _, route := range c.routes {
				checkRoute(t, c, route)
			}
			checkFan(t, routeWith(t, p, l, tc.x, numberByOldKey), tc.old, 2)
		})
	}
}
