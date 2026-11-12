package layered

import (
	"fmt"
	"reflect"
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
	r, err := Route(p, layers, x)
	if err != nil {
		t.Fatal(err)
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
