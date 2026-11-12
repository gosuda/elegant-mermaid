package layout

import (
	"bytes"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func assertCellText(t *testing.T, s scene.Scene, texts ...string) {
	t.Helper()
	rendered, err := cells.Render(s, cells.Options{})
	if err != nil {
		t.Fatal(err)
	}
	if rendered.RefusedClusters != 0 {
		t.Fatalf("refused %d clusters:\n%s", rendered.RefusedClusters, rendered.Text)
	}
	for _, text := range texts {
		if !bytes.Contains(rendered.Text, []byte(text)) {
			t.Fatalf("missing %q:\n%s", text, rendered.Text)
		}
	}
}
func TestCellLabelGutterOrientation(t *testing.T) {
	in := step14Input()
	in.Labels = []Label{{ID: "e0.label", Owner: "e0", Text: "yes"}}
	for _, d := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
		in.Direction = d
		s := step14Scene(t, in)
		if s.Labels[0].Rect.W != 3 || s.Labels[0].Rect.H != 1 {
			t.Fatal("gutter changed upright text dimensions", s.Labels)
		}
		assertCellText(t, s, "yes")
	}
}
func TestGroupEntryTitleGutter(t *testing.T) {
	in := groupRouteInput()
	in.Boxes[0].Direction = ""
	in.Labels[0].Text = "Title"
	in.Routes = append(in.Routes, Route{ID: "entry", From: "S", To: "A", Orthogonal: true})
	assertCellText(t, step14Scene(t, in), "Title")
}
func TestReversedGroupTopTitleGutter(t *testing.T) {
	in := groupRouteInput()
	in.Boxes[0].Direction = ""
	in.Labels[0].Text = "Title"
	in.Routes = []Route{{ID: "out", From: "S", To: "X", Orthogonal: true}, {ID: "back", From: "X", To: "S", Orthogonal: true}}
	s := step14Scene(t, in)
	if len(s.Routes[1].Points) < 7 {
		t.Fatal("reversed target top must use boundary gutter", s.Routes[1].Points)
	}
	assertCellText(t, s, "Title")
}
func TestDirectedGroupTitlesStayUpright(t *testing.T) {
	for _, d := range []string{"TB", "BT", "LR", "RL"} {
		in := groupRouteInput()
		in.Boxes[0].Direction = d
		in.Labels[0].Text = "Title"
		assertCellText(t, step14Scene(t, in), "Title")
	}
}

func TestImplicitGroupTitleGeometry(t *testing.T) {
	for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
		in := groupRouteInput()
		in.Labels = nil
		in.Direction = direction
		in.Boxes = append(in.Boxes, Box{ID: "Outer", Role: scene.RoleGroup})
		in.Boxes[0].Parent = "Outer"
		in.Groups = append(in.Groups, Group{ID: "Outer"})
		s := step14Scene(t, in)
		if len(s.Labels) != 0 {
			t.Fatal("implicit titles must not create canonical records", s.Labels)
		}
		assertCellText(t, s, "S", "Outer")
	}
}
