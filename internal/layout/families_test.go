package layout

import (
	"bytes"
	"os"
	"strconv"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	random "github.com/gosuda/elegant-mermaid/tools/randgraph/gen"
)

func TestOneFamilyPerKind(t *testing.T) {
	for _, family := range Families {
		in := Input{Kind: family.Kind, Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}}}
		vector, _, err := Layout(in)
		if err != nil {
			t.Fatal(err)
		}
		in.Profile = scene.ProfileCell
		cell, _, err := Layout(in)
		if err != nil {
			t.Fatal(err)
		}
		if len(vector.Boxes) != len(cell.Boxes) || vector.Boxes[0].ID != cell.Boxes[0].ID {
			t.Fatal("profile changed model identities")
		}
	}
}

func TestRandomLayeredValidity(t *testing.T) {
	for i := range 200 {
		source, err := random.Source("layered", i)
		if err != nil {
			t.Fatal(err)
		}
		in := randomInput(source)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
				in.Profile = profile
				in.Direction = direction
				assertValidLayout(t, i, in)
			}
		}
	}
}

func assertValidLayout(t *testing.T, index int, in Input) {
	t.Helper()
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(index, err)
	}
	clause, failed, err := s.Validate()
	if err != nil || failed {
		t.Fatalf("case %d %v %v: %v %v", index, in.Profile, in.Direction, clause, err)
	}
}

func randomInput(source string) Input {
	in := Input{Kind: "flowchart", Options: scene.DefaultOptions()}
	for _, line := range strings.Split(source, "\n")[1:] {
		if strings.Contains(line, " --> ") {
			ends := strings.Split(line, " --> ")
			in.Routes = append(in.Routes, Route{ID: "e" + strconv.Itoa(len(in.Routes)), From: ends[0], To: ends[1], Orthogonal: true})
		} else if id, text, ok := strings.Cut(line, "["); ok {
			in.Boxes = append(in.Boxes, Box{ID: id, Exclusive: true})
			in.Labels = append(in.Labels, Label{ID: id + ".label", Owner: id, Text: strings.TrimSuffix(text, "]")})
		}
	}
	return in
}

func TestTwoNodeGolden(t *testing.T) {
	in := Input{Kind: "flowchart", Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []Route{{ID: "e0", From: "A", To: "B", Orthogonal: true, MinLength: 1}}, Labels: []Label{{ID: "e0.label", Owner: "e0", Text: "yes"}}}
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	want, err := os.ReadFile("../../spec/golden/two-node.layout.json")
	if err != nil {
		t.Fatal(err)
	}
	if got := s.AppendJSON(nil); !bytes.Equal(got, want) {
		t.Fatalf("got:\n%s\nwant:\n%s", got, want)
	}
}

func TestExclusiveNodeTextIsNotSeparateLabel(t *testing.T) {
	in := Input{Kind: "flowchart", Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}}, Labels: []Label{{ID: "A.label", Owner: "A", Text: "Explicit label"}}}
	s, _, err := Layout(in)
	if err != nil {
		t.Fatal(err)
	}
	if len(s.Labels) != 0 {
		t.Fatal("exclusive-box text must not be a separate clearance object")
	}
	group := s.Groups[0]
	text, ok := group.Items[1].(*scene.Text)
	if !ok || text.Lines[0][0].Text != "Explicit label" {
		t.Fatal("missing node text")
	}
	inside, err := geom.Contains(s.Boxes[0].Rect, text.Rect)
	if err != nil || !inside {
		t.Fatal("node text must be inside its owner")
	}
}

func TestFlowchartEdgeScene(t *testing.T) {
	cases := []struct {
		source  string
		markers []string
		line    scene.LineStyle
		width   scene.WidthKind
	}{
		{"A --- B", nil, scene.LineSolid, scene.WidthNormal},
		{"A <--> B", []string{"point", "point"}, scene.LineSolid, scene.WidthNormal},
		{"A o--x B", nil, scene.LineSolid, scene.WidthNormal},
		{"A o--o B", []string{"circle", "circle"}, scene.LineSolid, scene.WidthNormal},
		{"A x--x B", []string{"cross", "cross"}, scene.LineSolid, scene.WidthNormal},
		{"A -.-> B", []string{"point"}, scene.LineDotted, scene.WidthNormal},
		{"A ==> B", []string{"point"}, scene.LineSolid, scene.WidthEmphasis},
	}
	for _, c := range cases {
		t.Run(c.source, func(t *testing.T) {
			s := edgeScene(t, c.source)
			items := s.Groups[0].Items
			if len(items) != 1+len(c.markers) {
				t.Fatalf("items: %#v", items)
			}
			line, ok := items[0].(*scene.Polyline)
			if !ok || line.Line != c.line || line.Width.Kind != c.width {
				t.Fatalf("stroke: %#v", items[0])
			}
			assertEdgeMarkers(t, s, c.markers)
		})
	}
}

func edgeScene(t *testing.T, source string) scene.Scene {
	t.Helper()
	in := Input{Kind: "flowchart", Direction: scene.DirectionLR, Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []Route{handEdge(source)}}
	s, err := handPipeline(in)
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func handEdge(source string) Route {
	r := Route{ID: "e0", From: "A", To: "B", MarkerStart: "none", MarkerEnd: "none", Line: "normal", MinLength: 1}
	switch source {
	case "A --> B":
		r.MarkerEnd = "point"
	case "A <--> B":
		r.MarkerStart, r.MarkerEnd = "point", "point"
	case "A o--o B":
		r.MarkerStart, r.MarkerEnd = "circle", "circle"
	case "A x--x B":
		r.MarkerStart, r.MarkerEnd = "cross", "cross"
	case "A -.-> B":
		r.MarkerEnd, r.Line = "point", "dotted"
	case "A ==> B":
		r.MarkerEnd, r.Line = "point", "thick"
	case "A ---> B":
		r.MarkerEnd, r.MinLength = "point", 2
	}
	return r
}

func assertEdgeMarkers(t *testing.T, s scene.Scene, names []string) {
	t.Helper()
	points := s.Routes[0].Points
	for i, name := range names {
		m, ok := s.Groups[0].Items[i+1].(*scene.MarkerRef)
		if !ok || m.Marker != name {
			t.Fatalf("marker %d: %#v", i, s.Groups[0].Items[i+1])
		}
		want, axis := points[len(points)-1], scene.AxisPlusX
		if len(names) == 2 && i == 0 {
			want, axis = points[0], scene.AxisMinusX
		}
		if m.At != want || m.Axis != axis {
			t.Fatalf("marker placement: %#v", m)
		}
	}
}

func TestFlowchartExtraDashRank(t *testing.T) {
	short, long := edgeScene(t, "A --> B"), edgeScene(t, "A ---> B")
	if long.Boxes[1].Rect != short.Boxes[1].Rect {
		t.Fatalf("dash count must not change ranks: %v %v", short.Boxes, long.Boxes)
	}
}

func TestReversedEdgeMarkers(t *testing.T) {
	in := Input{Kind: "flowchart", Direction: scene.DirectionLR, Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []Route{handEdge("A --> B"), {ID: "e1", From: "B", To: "A", MarkerStart: "circle", MarkerEnd: "circle", MinLength: 1}}}
	s, err := handPipeline(in)
	if err != nil {
		t.Fatal(err)
	}
	points := s.Routes[1].Points
	start := s.Groups[1].Items[1].(*scene.MarkerRef)
	end := s.Groups[1].Items[2].(*scene.MarkerRef)
	if start.At != points[0] || start.Axis != scene.AxisPlusX || end.At != points[len(points)-1] || end.Axis != scene.AxisMinusX {
		t.Fatalf("reversed markers: %#v %#v", start, end)
	}
}

func handPipeline(in Input) (scene.Scene, error) {
	input := layered.Input{Kind: in.Kind}
	for _, box := range in.Boxes {
		input.Boxes = append(input.Boxes, scene.Box{ID: box.ID, Exclusive: box.Exclusive})
	}
	for _, route := range in.Routes {
		start, end := route.MarkerStart, route.MarkerEnd
		if start == "none" {
			start = ""
		}
		if end == "none" {
			end = ""
		}
		input.Routes = append(input.Routes, scene.Route{ID: route.ID, From: route.From, To: route.To, Orthogonal: true})
		input.Edges = append(input.Edges, layered.EdgeOptions{MarkerStart: start, MarkerEnd: end, Stroke: route.Line, MinLength: edgeMinLength(in.Kind, route)})
	}
	options := in.Options
	options.Direction = in.Direction
	return layered.LayoutFamily(input, layered.Options{Scene: options})
}

func TestUnlabelledRanksIgnoreSyntax(t *testing.T) {
	sources := []string{"A --- B", "A <--> B", "A o--x B", "A -.-> B", "A ==> B", "A ---> B"}
	for _, source := range sources {
		t.Run(source, func(t *testing.T) {
			in, ok := inputSource(t, []byte("flowchart LR\n"+source+"\n"))
			if !ok {
				t.Fatal("source rejected")
			}
			s, _, err := Layout(in)
			if err != nil {
				t.Fatal(err)
			}
			if s.Boxes[1].Rect.X-s.Boxes[0].Rect.X-s.Boxes[0].Rect.W != 3072 {
				t.Fatal("unlabelled edges must have minimum length one")
			}
		})
	}
}
