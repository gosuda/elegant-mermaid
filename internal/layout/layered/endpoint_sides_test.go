package layered

import (
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var rerouteSides = [][2]geom.Side{
	{geom.SideTop, geom.SideBottom},
	{geom.SideBottom, geom.SideTop},
	{geom.SideLeft, geom.SideRight},
	{geom.SideRight, geom.SideLeft},
}

func rerouteFixture(from, to geom.Side, forced map[int]bool) Input {
	routes := []scene.Route{
		{ID: "e0", From: "A", To: "B", Orthogonal: true, MarkerEnd: "point"},
		{ID: "e1", From: "A", To: "B", Orthogonal: true, MarkerEnd: "point"},
		{ID: "e2", From: "B", To: "A", Orthogonal: true, MarkerEnd: "point"},
		{ID: "e3", From: "A", To: "obstacle", Orthogonal: true, MarkerEnd: "point"},
		{ID: "e4", From: "obstacle", To: "B", Orthogonal: true, MarkerEnd: "point"},
	}
	edges := make([]EdgeOptions, len(routes))
	for i := range edges {
		edges[i] = EdgeOptions{MarkerEnd: "point", Stroke: "normal", MinLength: 1}
		if forced[i] {
			edges[i].FromSide, edges[i].ToSide = from, to
		}
	}
	return Input{
		Kind:   "flowchart",
		Boxes:  []scene.Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}, {ID: "obstacle", Exclusive: true}},
		Routes: routes,
		Edges:  edges,
		Labels: []scene.Label{{ID: "e0.label", Owner: "e0", Text: "relation"}},
		Text:   []string{"A", "B", "obstacle"},
	}
}

func rerouteOptions(profile scene.Profile, direction scene.Direction) Options {
	o := scene.DefaultOptions()
	o.Profile = profile
	o.Direction = direction
	o.Thoroughness = 1
	return Options{Scene: o}
}

func reroutedScene(t *testing.T, in Input, opts Options) scene.Scene {
	t.Helper()
	base, err := LayoutFamily(in, opts)
	if err != nil {
		t.Fatalf("LayoutFamily: %v", err)
	}
	out, err := RerouteEndpoints(in, base)
	if err != nil {
		t.Fatalf("RerouteEndpoints: %v", err)
	}
	if clause, failed, err := out.Validate(); err != nil || failed {
		t.Fatalf("rerouted scene fails validation: %v %v %v", clause.ID, clause.Message, err)
	}
	return out
}

func boxRectByID(s scene.Scene, id string) geom.Rect {
	for _, box := range s.Boxes {
		if box.ID == id {
			return box.Rect
		}
	}
	return geom.Rect{}
}

func scopeContains(s scene.Scene, id, endpoint string) bool {
	parents := map[string]bool{}
	for box, fuel := endpoint, len(s.Boxes)+1; box != "" && fuel > 0; fuel-- {
		parents[box] = true
		box = boxParent(s, box)
	}
	return parents[id]
}

func boxParent(s scene.Scene, id string) string {
	for _, box := range s.Boxes {
		if box.ID == id {
			return box.Parent
		}
	}
	return ""
}

func facePoint(rect geom.Rect, side geom.Side) geom.Point {
	switch side {
	case geom.SideTop:
		return geom.Point{X: rect.X + rect.W/2, Y: rect.Y}
	case geom.SideBottom:
		return geom.Point{X: rect.X + rect.W/2, Y: rect.Y + rect.H}
	case geom.SideLeft:
		return geom.Point{X: rect.X, Y: rect.Y + rect.H/2}
	case geom.SideRight:
		return geom.Point{X: rect.X + rect.W, Y: rect.Y + rect.H/2}
	}
	return geom.Point{}
}

func outwardVector(side geom.Side) (int, int) {
	switch side {
	case geom.SideTop:
		return 0, -1
	case geom.SideBottom:
		return 0, 1
	case geom.SideLeft:
		return -1, 0
	case geom.SideRight:
		return 1, 0
	}
	return 0, 0
}

func specAxis(a, b geom.Point) scene.Axis {
	if b.X < a.X {
		return scene.AxisMinusX
	}
	if b.X > a.X {
		return scene.AxisPlusX
	}
	if b.Y < a.Y {
		return scene.AxisMinusY
	}
	return scene.AxisPlusY
}

func sign64(v int64) int {
	switch {
	case v < 0:
		return -1
	case v > 0:
		return 1
	}
	return 0
}

func routeByID(s scene.Scene, id string) *scene.Route {
	for i := range s.Routes {
		if s.Routes[i].ID == id {
			return &s.Routes[i]
		}
	}
	return nil
}

type boxFace struct {
	boxID string
	side  geom.Side
}

func faceMidpoint(s scene.Scene, f boxFace) geom.Point {
	return facePoint(boxRectByID(s, f.boxID), f.side)
}

func checkFaceEndpoints(t *testing.T, s scene.Scene, id string, points []geom.Point, from, to boxFace) {
	t.Helper()
	if points[0] != faceMidpoint(s, from) {
		t.Fatalf("route %s first point %v is not the %v face midpoint %v of %v", id, points[0], from.side, faceMidpoint(s, from), from.boxID)
	}
	last := points[len(points)-1]
	if last != faceMidpoint(s, to) {
		t.Fatalf("route %s last point %v is not the %v face midpoint %v of %v", id, last, to.side, faceMidpoint(s, to), to.boxID)
	}
}

func checkOutwardStubs(t *testing.T, id string, sides [2]geom.Side, points []geom.Point) {
	t.Helper()
	fd, fy := outwardVector(sides[0])
	if sign64(int64(points[1].X)-int64(points[0].X)) != fd || sign64(int64(points[1].Y)-int64(points[0].Y)) != fy {
		t.Fatalf("route %s must leave %v outward: %v then %v", id, sides[0], points[0], points[1])
	}
	td, ty := outwardVector(sides[1])
	last := points[len(points)-1]
	prev := points[len(points)-2]
	if sign64(int64(prev.X)-int64(last.X)) != td || sign64(int64(prev.Y)-int64(last.Y)) != ty {
		t.Fatalf("route %s must enter %v against its outward vector: %v then %v", id, sides[1], prev, last)
	}
}

func checkRouteInCanvas(t *testing.T, id string, points []geom.Point, canvas geom.Size) {
	t.Helper()
	for i, p := range points {
		if p.X < 0 || p.Y < 0 || p.X > canvas.W || p.Y > canvas.H {
			t.Fatalf("route %s point %d %v must stay inside canvas %v", id, i, p, canvas)
		}
	}
}

func unrelatedExclusiveBox(s scene.Scene, box scene.Box, owner, target string) bool {
	return box.Exclusive && !scopeContains(s, box.ID, owner) && !scopeContains(s, box.ID, target)
}

func hitRect(t *testing.T, id, name string, points []geom.Point, rect geom.Rect) bool {
	t.Helper()
	hits, err := geom.PolylineHitsRect(points, rect)
	if err != nil {
		t.Fatalf("route %s clearance check against %s: %v", id, name, err)
	}
	return hits
}

func checkRouteClearance(t *testing.T, s scene.Scene, id string, points []geom.Point, owner, target string) {
	t.Helper()
	for _, box := range s.Boxes {
		if !unrelatedExclusiveBox(s, box, owner, target) {
			continue
		}
		if hitRect(t, id, box.ID, points, box.Rect) {
			t.Fatalf("route %s must avoid open interior of unrelated box %s %v", id, box.ID, box.Rect)
		}
	}
	for _, label := range s.Labels {
		if hitRect(t, id, "label "+label.ID, points, label.Rect) {
			t.Fatalf("route %s must avoid label %s %v", id, label.ID, label.Rect)
		}
	}
}

func assertForcedRoute(t *testing.T, s scene.Scene, id, owner, target string, sides [2]geom.Side) {
	t.Helper()
	route := routeByID(s, id)
	if route == nil {
		t.Fatalf("route %s missing", id)
	}
	points := route.Points
	if len(points) < 3 {
		t.Fatalf("route %s forced on both faces must have stubs and ports: %d points", id, len(points))
	}
	from, to := boxFace{boxID: owner, side: sides[0]}, boxFace{boxID: target, side: sides[1]}
	checkFaceEndpoints(t, s, id, points, from, to)
	checkOutwardStubs(t, id, sides, points)
	if !geom.IsOrthogonal(points) {
		t.Fatalf("route %s must be orthogonal: %v", id, points)
	}
	checkRouteInCanvas(t, id, points, s.Canvas)
	checkRouteClearance(t, s, id, points, owner, target)
	assertForcedMarkers(t, s, id, points)
}

func assertForcedMarkers(t *testing.T, s scene.Scene, id string, points []geom.Point) {
	t.Helper()
	var markers []*scene.MarkerRef
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleEdge || group.Owner != id {
			continue
		}
		for _, item := range group.Items {
			if marker, ok := item.(*scene.MarkerRef); ok {
				markers = append(markers, marker)
			}
		}
	}
	if len(markers) != 1 {
		t.Fatalf("route %s must carry exactly one marker after rerouting: %d", id, len(markers))
	}
	last := points[len(points)-1]
	if markers[0].At != last {
		t.Fatalf("route %s marker sits at %v; the rerouted route ends at %v", id, markers[0].At, last)
	}
	if want := specAxis(points[len(points)-2], last); markers[0].Axis != want {
		t.Fatalf("route %s marker axis is %v; the final segment %v to %v needs %v", id, markers[0].Axis, points[len(points)-2], last, want)
	}
}

func TestRerouteEndpointsForcedFaces(t *testing.T) {
	all := map[int]bool{0: true, 1: true, 2: true, 3: true, 4: true}
	ends := [][2]string{{"A", "B"}, {"A", "B"}, {"B", "A"}, {"A", "obstacle"}, {"obstacle", "B"}}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
			for _, sides := range rerouteSides {
				in := rerouteFixture(sides[0], sides[1], all)
				out := reroutedScene(t, in, rerouteOptions(profile, direction))
				for i, route := range out.Routes {
					assertForcedRoute(t, out, route.ID, ends[i][0], ends[i][1], sides)
				}
				if !slices.Equal(out.Routes[0].Points, out.Routes[1].Points) {
					t.Fatalf("%v %v: identical forced routes diverged: %v vs %v", profile, direction, out.Routes[0].Points, out.Routes[1].Points)
				}
			}
		}
	}
}

func TestRerouteEndpointsAgainstRanking(t *testing.T) {
	in := rerouteFixture(geom.SideTop, geom.SideBottom, map[int]bool{0: true})
	opts := rerouteOptions(scene.ProfileVector, scene.DirectionTB)
	plainIn := rerouteFixture(geom.SideNone, geom.SideNone, nil)
	plain := reroutedScene(t, plainIn, opts)
	out := reroutedScene(t, in, opts)
	for i, box := range plain.Boxes {
		if box.Rect != out.Boxes[i].Rect {
			t.Fatalf("side metadata must not move box %s: %v vs %v", box.ID, box.Rect, out.Boxes[i].Rect)
		}
	}
	if plain.Canvas != out.Canvas {
		t.Fatalf("side metadata must not change the canvas: %v vs %v", plain.Canvas, out.Canvas)
	}
	assertForcedRoute(t, out, "e0", "A", "B", rerouteSides[0])
	if slices.Equal(plain.Routes[0].Points, out.Routes[0].Points) {
		t.Fatal("endpoint sides must change the drawn route of e0")
	}
	aRect, bRect := boxRectByID(out, "A"), boxRectByID(out, "B")
	if plain.Routes[0].Points[0] == facePoint(aRect, geom.SideTop) {
		t.Fatal("the ordinary ranked route must not already leave A through its top face")
	}
	if plain.Routes[0].Points[len(plain.Routes[0].Points)-1] == facePoint(bRect, geom.SideBottom) {
		t.Fatal("the ordinary ranked route must not already enter B through its bottom face")
	}
	for i := 1; i < len(out.Routes); i++ {
		if !slices.Equal(plain.Routes[i].Points, out.Routes[i].Points) {
			t.Fatalf("route %s has no sides and must keep its ordinary points", out.Routes[i].ID)
		}
	}
}

func TestRerouteEndpointsExclusiveAncestor(t *testing.T) {
	in := Input{
		Kind:   "flowchart",
		Boxes:  []scene.Box{{ID: "S", Role: scene.RoleGroup, Exclusive: true}, {ID: "A", Parent: "S", Exclusive: true}, {ID: "B", Exclusive: true}},
		Routes: []scene.Route{{ID: "e0", From: "A", To: "B", Orthogonal: true, MarkerEnd: "point"}},
		Edges:  []EdgeOptions{{MarkerEnd: "point", Stroke: "normal", MinLength: 1, FromSide: geom.SideTop, ToSide: geom.SideBottom}},
		Text:   []string{"S", "A", "B"},
	}
	opts := rerouteOptions(scene.ProfileVector, scene.DirectionTB)
	out := reroutedScene(t, in, opts)
	assertForcedRoute(t, out, "e0", "A", "B", rerouteSides[0])
	stub := out.Routes[0].Points[1]
	frame := boxRectByID(out, "S")
	if !pointInOpenInterior(stub, frame) {
		t.Fatalf("the outward stub %v must pass through the exclusive ancestor frame %v; blocking it would fail the route", stub, frame)
	}
}

func pointInOpenInterior(p geom.Point, r geom.Rect) bool {
	return int64(r.X) < int64(p.X) && int64(p.X) < int64(r.X)+int64(r.W) &&
		int64(r.Y) < int64(p.Y) && int64(p.Y) < int64(r.Y)+int64(r.H)
}

func samePrimitive(t *testing.T, owner string, base, out scene.Primitive) {
	t.Helper()
	switch p := base.(type) {
	case *scene.Polyline:
		other, ok := out.(*scene.Polyline)
		if !ok || !slices.Equal(p.Points, other.Points) {
			t.Fatalf("polyline of group %s moved without endpoint sides", owner)
		}
	case *scene.MarkerRef:
		other, ok := out.(*scene.MarkerRef)
		if !ok || p.At != other.At || p.Axis != other.Axis {
			t.Fatalf("marker of group %s moved without endpoint sides", owner)
		}
	}
}

func TestRerouteEndpointsUnforcedUnchanged(t *testing.T) {
	in := rerouteFixture(geom.SideNone, geom.SideNone, nil)
	opts := rerouteOptions(scene.ProfileVector, scene.DirectionTB)
	base, err := LayoutFamily(in, opts)
	if err != nil {
		t.Fatal(err)
	}
	out, err := RerouteEndpoints(in, base)
	if err != nil {
		t.Fatal(err)
	}
	for i := range base.Routes {
		if !slices.Equal(base.Routes[i].Points, out.Routes[i].Points) {
			t.Fatalf("route %s moved without endpoint sides", out.Routes[i].ID)
		}
	}
	for g, group := range base.Groups {
		for item, primitive := range group.Items {
			samePrimitive(t, group.Owner, primitive, out.Groups[g].Items[item])
		}
	}
}
