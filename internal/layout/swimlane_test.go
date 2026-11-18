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
