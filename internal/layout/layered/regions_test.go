package layered

import (
	"errors"
	"math"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var testMinima = frameMinima{border: 1, padding: 2, title: 1}

func TestRegionSolverKeepsEmptyBandsAndUnionSpans(t *testing.T) {
	c, err := solveRegions(regionProblem{
		parents: []int{-1, 0, 0, 0, 0, 0},
		sets:    []localRegionSet{{parent: 0, regions: []int{1, 2, 3, 4, 5}}},
		reservations: []regionReservation{
			{group: 2, left: -17, right: 43, span: rankSpan{2, 9}},
			{group: 4, left: 800, right: 803, span: rankSpan{0, 1}},
		},
		minima: testMinima,
	})
	if err != nil {
		t.Fatal(err)
	}
	for _, g := range []int{1, 3, 5} {
		if c.widths[g] != 7 {
			t.Fatalf("empty band %d width %d, want 7", g, c.widths[g])
		}
	}
	for i, band := range c.bands {
		if band.span != (rankSpan{0, 9}) {
			t.Fatalf("band %d span %v, want union 0..9", band.group, band.span)
		}
		if i > 0 && c.bands[i-1].right > band.left {
			t.Fatalf("bands overlap: %v", c.bands)
		}
	}
	if c.origins[2] != 3+17 || c.widths[2] != 60+6 {
		t.Fatalf("footprint group: origin %d width %d", c.origins[2], c.widths[2])
	}
}

func TestRegionSolverNestedSetsFollowDeclaration(t *testing.T) {
	c, err := solveRegions(regionProblem{
		parents: []int{-1, 0, 0, 1, 1},
		sets:    []localRegionSet{{parent: 0, regions: []int{2, 1}}, {parent: 1, regions: []int{4, 3}}},
		reservations: []regionReservation{
			{group: 3, left: -9, right: 80, span: rankSpan{3, 5}},
			{group: 4, left: 200, right: 204, span: rankSpan{4, 6}},
		},
		minima: testMinima,
	})
	if err != nil {
		t.Fatal(err)
	}
	var order []int
	for _, band := range c.bands {
		order = append(order, band.group)
	}
	if len(order) != 4 || order[0] != 2 || order[1] != 1 || order[2] != 4 || order[3] != 3 {
		t.Fatalf("band order %v, want [2 1 4 3]", order)
	}
	if c.widths[1] < c.widths[3]+c.widths[4]+6 {
		t.Fatalf("outer width %d does not cover nested set %d+%d", c.widths[1], c.widths[3], c.widths[4])
	}
}

func TestRegionSolverRejectsInvalidMetadata(t *testing.T) {
	for _, parents := range [][]int{{1, 0}, {9}, {0}} {
		if _, err := solveRegions(regionProblem{parents: parents, minima: testMinima}); !errors.Is(err, ErrGraph) {
			t.Fatalf("parents %v accepted: %v", parents, err)
		}
	}
	parents := []int{-1, 0, 0, 1}
	for _, regions := range [][]int{{1, 1}, {1, 3}, {9}, {}} {
		problem := regionProblem{parents: parents, sets: []localRegionSet{{parent: 0, regions: regions}}, minima: testMinima}
		if _, err := solveRegions(problem); !errors.Is(err, ErrGraph) {
			t.Fatalf("regions %v accepted: %v", regions, err)
		}
	}
	overlapping := regionProblem{parents: parents, sets: []localRegionSet{{parent: 0, regions: []int{1}}, {parent: 0, regions: []int{2}}}, minima: testMinima}
	if _, err := solveRegions(overlapping); !errors.Is(err, ErrGraph) {
		t.Fatalf("two sets on one parent accepted: %v", err)
	}
	wide := regionProblem{parents: []int{-1, 0}, sets: []localRegionSet{{parent: 0, regions: []int{1}}}, reservations: []regionReservation{{group: 1, left: math.MinInt32, right: math.MaxInt32}}, minima: testMinima}
	if _, err := solveRegions(wide); !errors.Is(err, geom.ErrOverflow) {
		t.Fatalf("full-range reservation: %v", err)
	}
}

func regionInput() Input {
	in := Input{Kind: "state"}
	add := func(id, parent string, role scene.BoxRole) {
		in.Boxes = append(in.Boxes, scene.Box{ID: id, Parent: parent, Role: role})
		text := id
		if role == scene.RoleGroup && parent == "C" {
			text = ""
		}
		in.Text = append(in.Text, text)
	}
	add("C", "", scene.RoleGroup)
	add("A", "R0", scene.RoleNode)
	add("B", "R0", scene.RoleNode)
	add("D", "R1", scene.RoleNode)
	add("S", "", scene.RoleNode)
	add("R0", "C", scene.RoleGroup)
	add("R1", "C", scene.RoleGroup)
	in.Routes = []scene.Route{{ID: "e0", From: "A", To: "B"}, {ID: "e1", From: "S", To: "C"}, {ID: "e2", From: "B", To: "A"}}
	in.Edges = make([]EdgeOptions, len(in.Routes))
	in.RegionSets = []RegionSet{{Parent: 0, Regions: []int{1, 2}}}
	return in
}

func TestRegionLayoutPlacesBandsSideBySide(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s, err := LayoutFamily(regionInput(), Options{Scene: scene.Options{Profile: profile, Thoroughness: 1}})
		if err != nil {
			t.Fatalf("%v: %v", profile, err)
		}
		rects := map[string]geom.Rect{}
		for _, b := range s.Boxes {
			rects[b.ID] = b.Rect
		}
		requireBandsSideBySide(t, profile, rects)
	}
}

func requireBandsSideBySide(t *testing.T, profile scene.Profile, rects map[string]geom.Rect) {
	t.Helper()
	c, r0, r1 := rects["C"], rects["R0"], rects["R1"]
	if r0.Y != r1.Y || r0.H != r1.H {
		t.Fatalf("%v: regions do not share ranks: %v %v", profile, r0, r1)
	}
	if r0.X+r0.W > r1.X || r0.X < c.X || r1.X+r1.W > c.X+c.W {
		t.Fatalf("%v: bands overlap or escape: C=%v R0=%v R1=%v", profile, c, r0, r1)
	}
	for _, id := range []string{"A", "B"} {
		if a := rects[id]; a.X < r0.X || a.X+a.W > r0.X+r0.W {
			t.Fatalf("%v: %s=%v escapes R0=%v", profile, id, a, r0)
		}
	}
}

func TestRegionInputValidationAndProjection(t *testing.T) {
	in := regionInput()
	if err := validateRegionSets(in); err != nil {
		t.Fatal(err)
	}
	bad := regionInput()
	bad.RegionSets = []RegionSet{{Parent: 0, Regions: []int{1, 1}}}
	if err := validateRegionSets(bad); !errors.Is(err, ErrGraph) {
		t.Fatalf("duplicate region accepted: %v", err)
	}
	in.Boxes[0].Direction = "LR"
	sub := subgraphInput(in, "C")
	requireOwnerRetainedAsRoot(t, in, sub)
	requireProjectedSets(t, in, sub)
	collapsed := collapseSubgraph(in, "C")
	if sets, err := collapsedRegionSets(in, "C", collapsed); err != nil || len(sets) != 0 {
		t.Fatalf("collapsed owner keeps sets %v, %v", sets, err)
	}
}

func requireOwnerRetainedAsRoot(t *testing.T, in, sub Input) {
	t.Helper()
	if len(sub.Boxes) != len(in.Boxes)-1 || sub.Boxes[0].ID != "C" || sub.Boxes[0].Parent != "" || sub.Boxes[0].Direction != "" {
		t.Fatalf("region owner not retained as root: %+v", sub.Boxes)
	}
}

func requireProjectedSets(t *testing.T, in, sub Input) {
	t.Helper()
	sets, err := subgraphRegionSets(in, sub)
	if err != nil || len(sets) != 1 || sets[0].Parent != 0 || sets[0].Regions[0] != 1 || sets[0].Regions[1] != 2 {
		t.Fatalf("projected sets %v, %v", sets, err)
	}
}

func groupSourceInput() Input {
	in := Input{Kind: "state"}
	add := func(id, parent string, role scene.BoxRole) {
		in.Boxes = append(in.Boxes, scene.Box{ID: id, Parent: parent, Role: role})
		in.Text = append(in.Text, id)
	}
	add("Active", "", scene.RoleGroup)
	add("R0", "Active", scene.RoleGroup)
	add("R1", "Active", scene.RoleGroup)
	add("A", "R0", scene.RoleNode)
	add("B", "R0", scene.RoleNode)
	add("C", "R1", scene.RoleNode)
	add("D", "R1", scene.RoleNode)
	in.Routes = []scene.Route{{ID: "e0", From: "A", To: "B"}, {ID: "e1", From: "C", To: "D"}, {ID: "e2", From: "Active", To: "A"}}
	in.Edges = make([]EdgeOptions, len(in.Routes))
	in.RegionSets = []RegionSet{{Parent: 0, Regions: []int{1, 2}}}
	return in
}

var groupSourceStartEdges = map[scene.Direction][2]string{
	scene.DirectionTB: {"top", "left"},
	scene.DirectionBT: {"bottom", "bottom"},
	scene.DirectionLR: {"left", "top"},
	scene.DirectionRL: {"right", "top"},
}

func groupSourceFrameAndRoute(t *testing.T, direction scene.Direction) (geom.Rect, []geom.Point) {
	t.Helper()
	o := scene.DefaultOptions()
	o.Direction = direction
	o.Thoroughness = 1
	s, err := LayoutFamily(groupSourceInput(), Options{Scene: o})
	if err != nil {
		t.Fatalf("%v: %v", direction, err)
	}
	var frame geom.Rect
	var points []geom.Point
	for i := range s.Boxes {
		if s.Boxes[i].ID == "Active" {
			frame = s.Boxes[i].Rect
		}
	}
	for i := range s.Routes {
		if s.Routes[i].ID == "e2" {
			points = s.Routes[i].Points
		}
	}
	if frame == (geom.Rect{}) || len(points) < 2 {
		t.Fatalf("%v: missing frame or route", direction)
	}
	return frame, points
}

func TestGroupSourceRouteStartsOnFrameEdge(t *testing.T) {
	for direction, edges := range groupSourceStartEdges {
		frame, points := groupSourceFrameAndRoute(t, direction)
		if !pointOnEdge(points[0], frame, edges[0]) {
			t.Fatalf("%v: first point %v not on %s edge of %v", direction, points[0], edges[0], frame)
		}
		if !pointOnEdge(points[1], frame, edges[1]) {
			t.Fatalf("%v: second point %v not on %s edge of %v", direction, points[1], edges[1], frame)
		}
		if !geom.IsOrthogonal(points) {
			t.Fatalf("%v: route not orthogonal: %v", direction, points)
		}
	}
}

func within(v, lo, hi int32) bool { return v >= lo && v <= hi }

func pointOnEdge(p geom.Point, r geom.Rect, edge string) bool {
	right, bottom := r.X+r.W, r.Y+r.H
	switch edge {
	case "top":
		return p.Y == r.Y && within(p.X, r.X, right)
	case "bottom":
		return p.Y == bottom && within(p.X, r.X, right)
	case "left":
		return p.X == r.X && within(p.Y, r.Y, bottom)
	case "right":
		return p.X == right && within(p.Y, r.Y, bottom)
	}
	return false
}
