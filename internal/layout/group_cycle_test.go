package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const groupCycleSource = "flowchart TB\n  n1[T]\n  subgraph g2[g2]\n    n3[X]\n  end\n  n3 --> n1\n  g2 --> n3\n  n1 --> g2\n"

func groupCycleScene(t *testing.T, profile scene.Profile) scene.Scene {
	t.Helper()
	d := ParseDiagram([]byte(groupCycleSource))
	for _, diagnostic := range d.Diagnostics {
		t.Fatalf("diagnostic: %+v", diagnostic)
	}
	in, err := d.Input(profile, scene.Options{Thoroughness: 1})
	if err != nil {
		t.Fatal(err)
	}
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func sceneRoute(t *testing.T, s scene.Scene, id string) []geom.Point {
	t.Helper()
	for _, r := range s.Routes {
		if r.ID == id {
			return r.Points
		}
	}
	t.Fatalf("no route %q", id)
	return nil
}

type frameRun struct{ y, farX int32 }

func frameRuns(points []geom.Point, frameLeft, frameTop int32) []frameRun {
	var runs []frameRun
	for i := 1; i < len(points); i++ {
		a, b := points[i-1], points[i]
		if a.Y != b.Y || a.Y <= frameTop || a.X == b.X || a.X != frameLeft && b.X != frameLeft {
			continue
		}
		runs = append(runs, frameRun{y: a.Y, farX: max(a.X, b.X)})
	}
	return runs
}

func orient(a, b, c geom.Point) int64 {
	n := int64(b.X-a.X)*int64(c.Y-a.Y) - int64(b.Y-a.Y)*int64(c.X-a.X)
	switch {
	case n < 0:
		return -1
	case n > 0:
		return 1
	}
	return 0
}

func polylineCrossings(p, q []geom.Point) int {
	count := 0
	for i := 1; i < len(p); i++ {
		for j := 1; j < len(q); j++ {
			if orient(p[i-1], p[i], q[j-1])*orient(p[i-1], p[i], q[j]) == -1 && orient(q[j-1], q[j], p[i-1])*orient(q[j-1], q[j], p[i]) == -1 {
				count++
			}
		}
	}
	return count
}

func TestReversedRunAtGroupTopStartsAtFrameLeft(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := groupCycleScene(t, profile)
		frame, n1 := sceneBox(t, s, "g2").Rect, sceneBox(t, s, "n1").Rect
		if n1.Y <= frame.Y {
			t.Fatalf("%v: n1 must lie below g2 so that e2 is drawn upward as a reversed run", profile)
		}
		e1, e2 := sceneRoute(t, s, "e1"), sceneRoute(t, s, "e2")
		first, second := frameRuns(e1, frame.X, frame.Y), frameRuns(e2, frame.X, frame.Y)
		if len(first) != 1 || len(second) != 1 {
			t.Fatalf("%v: each route needs one channel run on the frame_left gutter: %v %v", profile, first, second)
		}
		if first[0].y >= second[0].y {
			t.Errorf("%v: both runs start at frame_left and go right, so the lower decl (e1) takes the lower slot line: y(e1)=%d y(e2)=%d", profile, first[0].y, second[0].y)
		}
		descent := e1[len(e1)-1]
		if descent.X <= frame.X || descent.X >= second[0].farX || descent.Y <= second[0].y {
			t.Fatalf("%v: e1 must descend through the e2 run: %v", profile, descent)
		}
		if got := polylineCrossings(e1, e2); got != 1 {
			t.Errorf("%v: e1 descends through the higher e2 slot line, so they cross once, got %d", profile, got)
		}
	}
}
