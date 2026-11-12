package layered

import (
	"strconv"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestPipelineDirections(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
			in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []scene.Route{{ID: "e0", From: "A", To: "B", Orthogonal: true}}, Text: []string{"Start", "Choice"}}
			o := scene.DefaultOptions()
			o.Profile = profile
			o.Direction = direction
			s, err := LayoutFamily(in, Options{Scene: o})
			if err != nil {
				t.Fatal(err)
			}
			clause, failed, err := s.Validate()
			if err != nil || failed {
				t.Fatalf("%v %v: %v %v", profile, direction, clause, err)
			}
			if len(s.Groups) != 3 {
				t.Fatal("missing scene groups")
			}
		}
	}
}
func TestPipelineComponents(t *testing.T) {
	in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}}
	o := scene.DefaultOptions()
	s, err := LayoutFamily(in, Options{Scene: o})
	if err != nil {
		t.Fatal(err)
	}
	a, b := s.Boxes[0].Rect, s.Boxes[1].Rect
	if b.Y-a.Y-a.H != constant(o.Profile, "node_gap") || b.X != a.X {
		t.Fatalf("area-derived target stacks these components with one node gap: %v %v", a, b)
	}
}

func TestDirectionTransforms(t *testing.T) {
	in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []scene.Route{{ID: "e0", From: "A", To: "B", Orthogonal: true}}, Text: []string{"a<br>b<br>c", "d<br>e<br>f"}}
	o := scene.DefaultOptions()
	o.Profile = scene.ProfileCell
	views := make([]scene.Scene, 4)
	for d := range 4 {
		o.Direction = scene.Direction(d)
		var err error
		views[d], err = LayoutFamily(in, Options{Scene: o})
		if err != nil {
			t.Fatal(err)
		}
	}
	assertBoxDirectionTransforms(t, views)
	assertRouteDirectionTransforms(t, views)
}

func assertBoxDirectionTransforms(t *testing.T, views []scene.Scene) {
	t.Helper()
	for i, box := range views[0].Boxes {
		tb, bt, lr, rl := box.Rect, views[1].Boxes[i].Rect, views[2].Boxes[i].Rect, views[3].Boxes[i].Rect
		if tb.W != tb.H {
			t.Fatal("fixture must be symmetric")
		}
		expected := tb
		expected.X, expected.Y = tb.Y, tb.X
		expected.W, expected.H = tb.H, tb.W
		if lr != expected {
			t.Fatal("LR is not transposed TB")
		}
		expected = tb
		expected.Y = views[0].Canvas.H - tb.Y - tb.H
		if bt != expected {
			t.Fatal("BT is not reflected TB")
		}
		expected = lr
		expected.X = views[2].Canvas.W - lr.X - lr.W
		if rl != expected {
			t.Fatal("RL is not reflected LR")
		}
	}
}

func assertRouteDirectionTransforms(t *testing.T, views []scene.Scene) {
	t.Helper()
	for i, p := range views[0].Routes[0].Points {
		bt, lr, rl := views[1].Routes[0].Points[i], views[2].Routes[0].Points[i], views[3].Routes[0].Points[i]
		if lr.X != p.Y || lr.Y != p.X || bt.Y != views[0].Canvas.H-p.Y || rl.X != views[2].Canvas.W-lr.X {
			t.Fatal("route direction transform")
		}
	}
}

func TestDistinctNeighbourSizing(t *testing.T) {
	in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "A"}, {ID: "B"}, {ID: "C"}, {ID: "D"}, {ID: "E"}, {ID: "F"}}}
	for i, id := range []string{"B", "C", "D", "E", "F", "F"} {
		in.Routes = append(in.Routes, scene.Route{ID: "e" + strconv.Itoa(i), From: "A", To: id, Orthogonal: true})
	}
	o := scene.DefaultOptions()
	s, err := LayoutFamily(in, Options{Scene: o})
	if err != nil {
		t.Fatal(err)
	}
	if s.Boxes[0].Rect.W != 6*constant(o.Profile, "port_gap") {
		t.Fatal("five distinct proper neighbours require six port gaps; parallel direct edges share one neighbour")
	}
}
