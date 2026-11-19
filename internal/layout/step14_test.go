package layout

import (
	"errors"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func step14Input() Input {
	return Input{Kind: "flowchart", Profile: scene.ProfileCell, Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []Route{{ID: "e0", From: "A", To: "B", Orthogonal: true}}}
}

func step14Scene(t *testing.T, in Input) scene.Scene {
	t.Helper()
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	clause, failed, err := s.Validate()
	if err != nil || failed {
		t.Fatalf("invalid %v: %v", clause, err)
	}
	return s
}

func TestLabelNodes(t *testing.T) {
	in := step14Input()
	in.Labels = []Label{{ID: "e0.label", Owner: "e0", Text: "yes"}}
	s := step14Scene(t, in)
	if len(s.Labels) != 1 || s.Labels[0].Text != "yes" {
		t.Fatalf("labels: %v", s.Labels)
	}
	if s.Labels[0].Rect != (geom.Rect{X: 2, Y: 7, W: 3, H: 1}) {
		t.Fatalf("label rectangle: %v", s.Labels[0].Rect)
	}
	if s.Boxes[1].Rect.Y != 11 || s.Canvas != (geom.Size{W: 7, H: 15}) {
		t.Fatalf("label rank gap/canvas: %v %v", s.Boxes, s.Canvas)
	}
}

func TestSelfLoops(t *testing.T) {
	in := step14Input()
	in.Boxes = in.Boxes[:1]
	in.Routes[0].To = "A"
	s := step14Scene(t, in)
	want := []geom.Point{{X: 6, Y: 1}, {X: 7, Y: 1}, {X: 7, Y: 3}, {X: 6, Y: 3}}
	if len(s.Routes[0].Points) != len(want) {
		t.Fatal(s.Routes[0].Points)
	}
	for i, p := range want {
		if p != s.Routes[0].Points[i] {
			t.Fatalf("point %d: %v want %v", i, s.Routes[0].Points[i], p)
		}
	}
	if s.Boxes[0].Rect.H != 4 {
		t.Fatal("loop did not reserve two bands", s.Boxes)
	}
}

func TestTwoLabelledLoopsRenderEveryDirection(t *testing.T) {
	for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
		t.Run(direction.String(), func(t *testing.T) {
			in := step14Input()
			in.Direction = direction
			in.Options.Thoroughness = 1
			in.Routes = append(in.Routes,
				Route{ID: "back", From: "B", To: "A", Orthogonal: true},
				Route{ID: "loop1", From: "A", To: "A", Orthogonal: true},
				Route{ID: "loop2", From: "A", To: "A", Orthogonal: true})
			in.Labels = []Label{
				{ID: "A.label", Owner: "A", Text: "alpha"},
				{ID: "B.label", Owner: "B", Text: "beta"},
				{ID: "e0.label", Owner: "e0", Text: "forward"},
				{ID: "back.label", Owner: "back", Text: "back"},
				{ID: "loop1.label", Owner: "loop1", Text: "one"},
				{ID: "loop2.label", Owner: "loop2", Text: "two"},
			}
			assertCellText(t, step14Scene(t, in), "alpha", "beta", "forward", "back", "one", "two")
		})
	}
}

func TestReversedLanes(t *testing.T) {
	in := step14Input()
	in.Routes = append(in.Routes, Route{ID: "e1", From: "B", To: "A", Orthogonal: true})
	in.Options.Thoroughness = 1
	s := step14Scene(t, in)
	points := s.Routes[1].Points
	if len(points) != 6 {
		t.Fatalf("reversed route: %v", points)
	}
	if points[2].X != points[3].X || points[1].Y == points[4].Y {
		t.Fatal("lane runs require separate slots", points)
	}
	for _, b := range s.Boxes {
		if points[2].X <= b.Rect.X+b.Rect.W {
			t.Fatal("lane is not beyond nodes", points, b)
		}
	}
}

func TestClusters(t *testing.T) {
	in := step14Input()
	in.Boxes[0].Parent = "G"
	in.Boxes[1].Parent = "G"
	in.Boxes = append(in.Boxes, Box{ID: "G", Role: scene.RoleGroup})
	in.Groups = []Group{{ID: "G"}}
	in.Labels = append(in.Labels, Label{ID: "G.label", Owner: "G", Text: "Group"})
	s := step14Scene(t, in)
	for _, b := range s.Boxes[:2] {
		contains, err := geom.Contains(s.Boxes[2].Rect, b.Rect)
		if err != nil || !contains {
			t.Fatal("cluster containment", s.Boxes)
		}
	}
	if s.Groups[0].Role != scene.GroupRoleGroup || s.Groups[0].Owner != "G" {
		t.Fatal("frame paint order", s.Groups)
	}
}

func TestSubgraphDirection(t *testing.T) {
	in := step14Input()
	in.Boxes[0].Parent = "G"
	in.Boxes[1].Parent = "G"
	in.Boxes = append(in.Boxes, Box{ID: "G", Role: scene.RoleGroup, Direction: "LR"})
	in.Groups = []Group{{ID: "G"}}
	in.Labels = append(in.Labels, Label{ID: "G.label", Owner: "G", Text: "G"})
	s := step14Scene(t, in)
	if s.Boxes[0].Rect.Y != s.Boxes[1].Rect.Y || s.Boxes[0].Rect.X >= s.Boxes[1].Rect.X {
		t.Fatal("independent LR direction", s.Boxes)
	}
	in.Boxes = append(in.Boxes, Box{ID: "C", Exclusive: true})
	in.Routes = append(in.Routes, Route{ID: "e1", From: "B", To: "C", Orthogonal: true})
	_, ds, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	found := false
	for _, d := range ds {
		found = found || d.Code == "flowchart/subgraph-direction-ignored"
	}
	if !found {
		t.Fatal("crossing direction was not diagnosed", ds)
	}
}

func TestPacking(t *testing.T) {
	in := step14Input()
	in.Routes = nil
	in.Options.MaxWidth = 5
	s := step14Scene(t, in)
	if s.Boxes[0].Rect != (geom.Rect{X: 1, Y: 1, W: 5, H: 3}) || s.Boxes[1].Rect != (geom.Rect{X: 1, Y: 6, W: 5, H: 3}) {
		t.Fatal("5-column target should stack 5-column components with two-row gap", s.Boxes)
	}
	if s.Canvas != (geom.Size{W: 7, H: 10}) {
		t.Fatal(s.Canvas)
	}
}

func TestPortfolio(t *testing.T) {
	in := step14Input()
	in.Options.Thoroughness = 1
	first := step14Scene(t, in)
	in.Options.Thoroughness = 5
	all := step14Scene(t, in)
	if string(first.AppendJSON(nil)) == "" || all.Canvas != first.Canvas {
		t.Fatal("tied candidates changed incumbent geometry", first.Canvas, all.Canvas)
	}
	for i, b := range first.Boxes {
		if b.Rect != all.Boxes[i].Rect {
			t.Fatal("tie did not preserve incumbent", first.Boxes, all.Boxes)
		}
	}
}

func TestLayoutLimitsBeforeMeasurement(t *testing.T) {
	cases := []struct {
		name string
		in   Input
	}{
		{"nodes", step14Input()}, {"edges", step14Input()}, {"text bytes", step14Input()},
	}
	cases[0].in.Options.Limits.MaxNodes = 1
	cases[1].in.Options.Limits.MaxEdges = 1
	cases[1].in.Routes = append(cases[1].in.Routes, cases[1].in.Routes[0])
	cases[2].in.Options.Limits.MaxTextBytes = 1
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			_, _, err := Layout(tc.in)
			limit, ok := errors.AsType[*layered.LimitError](err)
			if !ok || !errors.Is(err, layered.ErrTooLarge) || limit.Resource != tc.name {
				t.Fatalf("limit error: %v", err)
			}
		})
	}
	in := step14Input()
	in.Options.Limits.MaxNodes = 2
	in.Options.Limits.MaxEdges = 1
	in.Options.Limits.MaxTextBytes = 2
	step14Scene(t, in)
}

func TestCellMeasurementNormalizesTerminalControls(t *testing.T) {
	in := step14Input()
	in.Routes = nil
	in.Boxes = in.Boxes[:1]
	in.Labels = []Label{{ID: "A.label", Owner: "A", Text: "x\x1b\u0085y"}}
	s := step14Scene(t, in)
	text := s.Groups[0].Items[1].(*scene.Text)
	if text.Lines[0][0].Text != "x\ufffd\ufffdy" {
		t.Fatal(text.Lines)
	}
	in.Profile = scene.ProfileVector
	s = step14Scene(t, in)
	text = s.Groups[0].Items[1].(*scene.Text)
	if !strings.Contains(text.Lines[0][0].Text, "\x1b") {
		t.Fatal("vector text was normalized")
	}
}
