package layout

import (
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func swimlaneScene(t *testing.T, src string, profile scene.Profile) scene.Scene {
	t.Helper()
	d := ParseDiagram([]byte(src))
	for _, diagnostic := range d.Diagnostics {
		t.Fatalf("diagnostic: %+v", diagnostic)
	}
	in, err := d.Input(profile, scene.Options{})
	if err != nil {
		t.Fatal(err)
	}
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	clause, failed, err := s.Validate()
	if err != nil || failed {
		t.Fatalf("validate: %v %v", clause, err)
	}
	return s
}

func sceneBox(t *testing.T, s scene.Scene, id string) scene.Box {
	t.Helper()
	for _, b := range s.Boxes {
		if b.ID == id {
			return b
		}
	}
	t.Fatalf("no box %q", id)
	return scene.Box{}
}

type spanOf func(geom.Rect) (start, end int32)

func rowSpan(r geom.Rect) (start, end int32) { return r.Y, r.Y + r.H }

func columnSpan(r geom.Rect) (start, end int32) { return r.X, r.X + r.W }

func swimlaneSource(direction string) string {
	return strings.Replace(threeLanes, "DIR", direction, 1)
}

const threeLanes = "swimlane-beta DIR\n  subgraph Customer\n    Browse[Browse catalogue]\n    Pay[Pay]\n  end\n  subgraph Warehouse\n    Pick[Pick items]\n    Ship[Ship order]\n  end\n  subgraph Finance\n    Invoice[Raise invoice]\n  end\n  Browse --> Pay\n  Pay --> Pick\n  Pick --> Ship\n  Pay --> Invoice\n"

func TestSwimlaneBandsTileCrossAxisInDeclarationOrder(t *testing.T) {
	cases := []struct {
		direction string
		span      spanOf
	}{{"LR", rowSpan}, {"RL", rowSpan}, {"TB", columnSpan}, {"BT", columnSpan}}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		for _, c := range cases {
			s := swimlaneScene(t, swimlaneSource(c.direction), profile)
			var previousEnd int32
			for i, lane := range []string{"Customer", "Warehouse", "Finance"} {
				start, end := c.span(sceneBox(t, s, lane).Rect)
				if i > 0 && start != previousEnd {
					t.Fatalf("%v %s: lane %s starts at %d, previous lane ends at %d", profile, c.direction, lane, start, previousEnd)
				}
				previousEnd = end
			}
		}
	}
}

func TestSwimlaneMembersSitInsideTheirBandWithTitleAndClearance(t *testing.T) {
	lanes := map[string][]string{"Customer": {"Browse", "Pay"}, "Warehouse": {"Pick", "Ship"}, "Finance": {"Invoice"}}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := swimlaneScene(t, swimlaneSource("LR"), profile)
		spacing, err := newLaneSpacing(profile)
		if err != nil {
			t.Fatal(err)
		}
		for lane, members := range lanes {
			start, end := rowSpan(sceneBox(t, s, lane).Rect)
			for _, member := range members {
				low, high := rowSpan(sceneBox(t, s, member).Rect)
				if int64(low) < int64(start)+spacing.title+spacing.clear || int64(high) > int64(end)-spacing.clear {
					t.Fatalf("%v: %s [%d,%d] leaves %s [%d,%d] short of title %d and clearance %d", profile, member, low, high, lane, start, end, spacing.title, spacing.clear)
				}
			}
		}
	}
}

func TestSwimlaneNestedGroupStaysInsideItsLane(t *testing.T) {
	s := swimlaneScene(t, "swimlane-beta LR\n  subgraph A\n    subgraph Inner\n      n\n    end\n    m\n  end\n  subgraph B\n    o\n  end\n  n --> o\n", scene.ProfileVector)
	lane := sceneBox(t, s, "A")
	inner := sceneBox(t, s, "Inner")
	if inner.Parent != "A" || inner.Role != scene.RoleGroup {
		t.Fatalf("inner group: %+v", inner)
	}
	start, end := rowSpan(lane.Rect)
	low, high := rowSpan(inner.Rect)
	if low < start || high > end {
		t.Fatalf("inner [%d,%d] leaves lane [%d,%d]", low, high, start, end)
	}
}

func TestSwimlaneLooseNodesFollowTheLaneStack(t *testing.T) {
	s := swimlaneScene(t, "swimlane-beta LR\n  subgraph A\n    a\n  end\n  loose\n  a --> loose\n", scene.ProfileVector)
	lane := sceneBox(t, s, "A")
	loose := sceneBox(t, s, "loose")
	if loose.Parent != "" {
		t.Fatalf("loose node got parent %q", loose.Parent)
	}
	if _, end := rowSpan(lane.Rect); loose.Rect.Y < end {
		t.Fatalf("loose node at %d overlaps the lane band ending at %d", loose.Rect.Y, end)
	}
}

func TestSwimlaneWithoutLanesIsTheLayeredLayout(t *testing.T) {
	src := "swimlane-beta LR\n  a --> b --> c\n"
	swim := swimlaneScene(t, src, scene.ProfileVector)
	flow := swimlaneScene(t, "flowchart LR\n  a --> b --> c\n", scene.ProfileVector)
	if len(swim.Boxes) != len(flow.Boxes) {
		t.Fatal("box count differs")
	}
	for i := range swim.Boxes {
		if swim.Boxes[i].Rect != flow.Boxes[i].Rect {
			t.Fatalf("box %s: %v != %v", swim.Boxes[i].ID, swim.Boxes[i].Rect, flow.Boxes[i].Rect)
		}
	}
}

func TestSwimlaneEmptyLaneKeepsItsBand(t *testing.T) {
	s := swimlaneScene(t, "swimlane-beta LR\n  subgraph Empty\n  end\n  subgraph Full\n    a --> b\n  end\n", scene.ProfileVector)
	empty := sceneBox(t, s, "Empty")
	full := sceneBox(t, s, "Full")
	if empty.Rect.H <= 0 {
		t.Fatalf("empty lane has no band: %v", empty.Rect)
	}
	if empty.Rect.Y+empty.Rect.H != full.Rect.Y {
		t.Fatalf("lanes do not touch: %v %v", empty.Rect, full.Rect)
	}
}

func TestSwimlaneCrossLaneRouteLabelLeavesEveryFrameInterior(t *testing.T) {
	s := swimlaneScene(t, "swimlane-beta LR\n  subgraph A\n    a\n  end\n  subgraph B\n    b\n  end\n  a -->|handoff| b\n", scene.ProfileVector)
	for _, label := range s.Labels {
		for _, b := range s.Boxes {
			if b.Role == scene.RoleGroup && meetsInterior(b.Rect, label.Rect) && !strictlyInside(b.Rect, label.Rect) {
				t.Fatalf("label %s straddles frame %s", label.ID, b.ID)
			}
		}
	}
}

const reversedCrossLane = `swimlane-beta LR
  subgraph L1[Community / Users]
  A1[Report issue]
  A2[Submit PR]
  end
  subgraph L2[GitHub System of Record]
  G1[GitHub Issues]
  G2[GitHub Pull Requests]
  G3["GitHub Projects\n(tracking + prioritization)"]
  end
  subgraph L3[Full-time OS Team\nOmkar • Darshan • Shubham]
  C2[Dev sync Tue/Thu\ntriage + plan complex items]
  C3[Implement work\nShubham: layout algorithms focus]
  C4[Peer review]
  end
  subgraph L4["Senior project members\n(pre-Mermaid Chart maintainers)"]
  end
  subgraph L5[Team Lead & Release Manager\nAshish Jain]
  R1[Owns release process\nplanning + cut release]
  R2[Biweekly release]
  end
  A1 --> G1 --> G3
  A2 --> G2 --> G3
  G3 --> C1 --> C3 --> G2
  G3 --> C2 --> C3
  R1 --> R2 --> G3
`

const forwardCrossBand = `swimlane-beta TB
  subgraph L0[Lane 0 cedar]
    N0_0[delta garnet]
    subgraph In0
    end
  end
  subgraph L1[Lane 1 delta]
    N1_3[amber delta]
  end
  subgraph L2[Lane 2 delta]
  end
  subgraph L3[Lane 3 cedar]
  end
  N1_0 --> N1_2
  N0_0 --> N1_3
  N0_0 -->|fjord garnet| N1_2
`

func TestSwimlaneRoutesBetweenBandsStayClearOfOtherNodes(t *testing.T) {
	for _, src := range []string{reversedCrossLane, forwardCrossBand} {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			swimlaneScene(t, src, profile)
		}
	}
}

func TestSwimlaneRebuiltRouteIsWhatTheEdgeGroupDraws(t *testing.T) {
	s := swimlaneScene(t, forwardCrossBand, scene.ProfileVector)
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleEdge {
			continue
		}
		for _, route := range s.Routes {
			if route.ID != group.Owner {
				continue
			}
			assertSwimlaneDrawnRoute(t, group, route)
		}
	}
}

func assertSwimlaneDrawnRoute(t *testing.T, group *scene.Group, route scene.Route) {
	t.Helper()
	for _, item := range group.Items {
		if line, ok := item.(*scene.Polyline); ok && !slices.Equal(line.Points, route.Points) {
			t.Fatalf("route %s: edge group draws %v, route is %v", route.ID, line.Points, route.Points)
		}
	}
}

func TestSwimlaneIsRegisteredAsOneFamily(t *testing.T) {
	count := 0
	for _, family := range Families {
		if family.Kind == "swimlane" {
			count++
		}
	}
	if count != 1 {
		t.Fatalf("swimlane registered %d times", count)
	}
}

func laneEndsBase(direction string) string {
	return strings.Replace("swimlane-beta DIR\n  subgraph A\n    a1[x]\n  end\n  subgraph B\n    b1[y]\n  end\n", "DIR", direction, 1)
}

func laneEndsNestedBase(direction string) string {
	return strings.Replace("swimlane-beta DIR\n  subgraph A\n    subgraph G\n      g1[x]\n    end\n  end\n  subgraph B\n    b1[y]\n  end\n", "DIR", direction, 1)
}

func laneEndsLoopRoute(t *testing.T, s scene.Scene, lane string) scene.Route {
	t.Helper()
	for _, route := range s.Routes {
		if route.From == lane && route.To == lane {
			return route
		}
	}
	t.Fatalf("no self-loop route on lane %q", lane)
	return scene.Route{}
}

func laneEndsTailMarker(t *testing.T, s scene.Scene, route scene.Route) scene.MarkerRef {
	t.Helper()
	last := route.Points[len(route.Points)-1]
	for _, group := range s.Groups {
		if group.Role != scene.GroupRoleEdge || group.Owner != route.ID {
			continue
		}
		for _, item := range group.Items {
			if marker, ok := item.(*scene.MarkerRef); ok && marker.At == last {
				return *marker
			}
		}
	}
	t.Fatalf("route %s has no marker at its last point %v", route.ID, last)
	return scene.MarkerRef{}
}

func topLevelLaneSet(s scene.Scene) map[string]bool {
	lanes := map[string]bool{}
	for _, box := range s.Boxes {
		if box.Role == scene.RoleGroup && box.Parent == "" {
			lanes[box.ID] = true
		}
	}
	return lanes
}

func assertLaneLoopEndsOnFrame(t *testing.T, profile scene.Profile, name, direction string, s scene.Scene, route scene.Route) {
	t.Helper()
	frame := sceneBox(t, s, route.From)
	var start, length, first, last int32
	if direction == "LR" || direction == "RL" {
		start, length = frame.Rect.Y, frame.Rect.H
		first, last = route.Points[0].Y, route.Points[len(route.Points)-1].Y
	} else {
		start, length = frame.Rect.X, frame.Rect.W
		first, last = route.Points[0].X, route.Points[len(route.Points)-1].X
	}
	if first != start+length || last != start+length {
		t.Fatalf("%v %s: route %s ends at (%d, %d), lane frame ends at %d", profile, name, route.ID, first, last, start+length)
	}
}

func assertLaneLoopsEndOnFrames(t *testing.T, profile scene.Profile, name, direction string, s scene.Scene) {
	t.Helper()
	lanes := topLevelLaneSet(s)
	loops := 0
	for _, route := range s.Routes {
		if route.From != route.To || !lanes[route.From] {
			continue
		}
		loops++
		assertLaneLoopEndsOnFrame(t, profile, name, direction, s, route)
	}
	if loops == 0 {
		t.Fatalf("%v %s: no lane self-loop route found", profile, name)
	}
}

func TestSwimlaneLaneSelfLoopsEndOnLaneFrame(t *testing.T) {
	cases := []struct {
		name, direction, src string
	}{
		{"lr", "LR", laneEndsBase("LR") + "  A --> A\n"},
		{"tb", "TB", laneEndsBase("TB") + "  A --> A\n"},
		{"rl", "RL", laneEndsBase("RL") + "  A --> A\n"},
		{"bt", "BT", laneEndsBase("BT") + "  A --> A\n"},
		{"label", "LR", laneEndsBase("LR") + "  A -->|x| A\n"},
		{"long label", "LR", laneEndsBase("LR") + "  A -->|a much longer loop label text| A\n"},
		{"double lr", "LR", laneEndsBase("LR") + "  A --> A\n  A --> A\n"},
		{"double tb", "TB", laneEndsBase("TB") + "  A --> A\n  A --> A\n"},
		{"last lane", "TB", laneEndsBase("TB") + "  B --> B\n"},
		{"two member", "LR", strings.Replace("swimlane-beta DIR\n  subgraph A\n    a1[x]\n    a2[z]\n  end\n  subgraph B\n    b1[y]\n  end\n", "DIR", "LR", 1) + "  A --> A\n"},
		{"empty lane", "LR", "swimlane-beta LR\n  subgraph A\n  end\n  subgraph B\n    b1[y]\n  end\n  A --> A\n"},
		{"loose", "LR", "swimlane-beta LR\n  subgraph A\n    a1[x]\n  end\n  c1[loose]\n  A --> A\n"},
	}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		for _, c := range cases {
			s := swimlaneScene(t, c.src, profile)
			assertLaneLoopsEndOnFrames(t, profile, c.name, c.direction, s)
		}
	}
}

func TestSwimlaneLaneSelfLoopGeometry(t *testing.T) {
	cases := []struct {
		name, direction string
		profile         scene.Profile
		points          []geom.Point
		marker          geom.Point
		axis            scene.Axis
	}{
		{"lr vector", "LR", scene.ProfileVector,
			[]geom.Point{{X: 1024, Y: 13568}, {X: 1024, Y: 11776}, {X: 2560, Y: 11776}, {X: 2560, Y: 13568}},
			geom.Point{X: 2560, Y: 13568}, scene.AxisPlusY},
		{"lr cell", "LR", scene.ProfileCell,
			[]geom.Point{{X: 1, Y: 14}, {X: 1, Y: 12}, {X: 3, Y: 12}, {X: 3, Y: 14}},
			geom.Point{}, 0},
		{"tb vector", "TB", scene.ProfileVector,
			[]geom.Point{{X: 13312, Y: 1024}, {X: 11520, Y: 1024}, {X: 11520, Y: 2560}, {X: 13312, Y: 2560}},
			geom.Point{X: 13312, Y: 2560}, scene.AxisPlusX},
		{"tb cell", "TB", scene.ProfileCell,
			[]geom.Point{{X: 16, Y: 1}, {X: 14, Y: 1}, {X: 14, Y: 3}, {X: 16, Y: 3}},
			geom.Point{}, 0},
	}
	for _, c := range cases {
		s := swimlaneScene(t, laneEndsBase(c.direction)+"  A --> A\n", c.profile)
		route := laneEndsLoopRoute(t, s, "A")
		if !slices.Equal(route.Points, c.points) {
			t.Fatalf("%s: got %v, want %v", c.name, route.Points, c.points)
		}
		if c.profile != scene.ProfileVector {
			continue
		}
		marker := laneEndsTailMarker(t, s, route)
		if marker.At != c.marker || marker.Axis != c.axis {
			t.Fatalf("%s: marker at %v axis %v, want at %v axis %v", c.name, marker.At, marker.Axis, c.marker, c.axis)
		}
	}
}

func TestSwimlaneLaneEndAttachmentKeepsOtherRoutes(t *testing.T) {
	cases := []struct {
		name         string
		src          string
		vector, cell []geom.Point
	}{
		{"lane to member", laneEndsBase("LR") + "  A --> a1\n",
			[]geom.Point{{X: 1024, Y: 6848}, {X: 1024, Y: 4096}, {X: 3852, Y: 4096}, {X: 3852, Y: 6784}, {X: 6540, Y: 6784}},
			[]geom.Point{{X: 1, Y: 6}, {X: 1, Y: 4}, {X: 4, Y: 4}, {X: 4, Y: 6}, {X: 7, Y: 6}}},
		{"member to lane", laneEndsBase("TB") + "  a1 --> A\n",
			[]geom.Point{{X: 6656, Y: 8704}, {X: 6656, Y: 11776}},
			[]geom.Point{{X: 7, Y: 9}, {X: 7, Y: 12}}},
		{"nested self", laneEndsNestedBase("LR") + "  G --> G\n",
			[]geom.Point{{X: 5772, Y: 12544}, {X: 5772, Y: 13312}, {X: 7308, Y: 13312}, {X: 7308, Y: 12544}},
			[]geom.Point{{X: 6, Y: 12}, {X: 6, Y: 13}, {X: 8, Y: 13}, {X: 8, Y: 12}}},
		{"nested to lane", laneEndsNestedBase("TB") + "  G --> A\n",
			[]geom.Point{{X: 8192, Y: 17152}, {X: 8192, Y: 20224}},
			[]geom.Point{{X: 8, Y: 17}, {X: 8, Y: 20}}},
		{"lane to other member", laneEndsBase("LR") + "  A --> b1\n",
			[]geom.Point{{X: 12507, Y: 6784}, {X: 15579, Y: 6784}, {X: 15579, Y: 17024}, {X: 16347, Y: 17024}},
			[]geom.Point{{X: 16, Y: 6}, {X: 19, Y: 6}, {X: 19, Y: 16}, {X: 20, Y: 16}}},
		{"lane to lane", laneEndsBase("LR") + "  A --> B\n",
			[]geom.Point{{X: 10892, Y: 6784}, {X: 13196, Y: 6784}, {X: 13196, Y: 17024}, {X: 13964, Y: 17024}},
			[]geom.Point{{X: 14, Y: 6}, {X: 16, Y: 6}, {X: 16, Y: 16}, {X: 17, Y: 16}}},
	}
	for _, c := range cases {
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			want := c.vector
			if profile == scene.ProfileCell {
				want = c.cell
			}
			s := swimlaneScene(t, c.src, profile)
			if len(s.Routes) != 1 {
				t.Fatalf("%v %s: got %d routes, want 1", profile, c.name, len(s.Routes))
			}
			if !slices.Equal(s.Routes[0].Points, want) {
				t.Fatalf("%v %s: got %v, want %v", profile, c.name, s.Routes[0].Points, want)
			}
		}
	}
}
