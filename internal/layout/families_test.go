package layout

import (
	"bytes"
	"os"
	"strconv"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
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
	in := Input{Kind: "flowchart", Options: scene.DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []Route{{ID: "e0", From: "A", To: "B", Orthogonal: true}}, Labels: []Label{{ID: "e0.label", Owner: "e0", Text: "yes"}}}
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
