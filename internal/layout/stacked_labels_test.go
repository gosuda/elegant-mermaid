package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestStackedRouteLabels(t *testing.T) {
	for _, kind := range []string{"forward", "reversed", "loop"} {
		t.Run(kind, func(t *testing.T) {
			in, owner := stackedInput(kind)
			s := step14Scene(t, in)
			assertLabelStack(t, s, owner)
			assertCellText(t, s, "one", "longer")
		})
	}
}

func stackedInput(kind string) (Input, string) {
	in := step14Input()
	owner := "e0"
	switch kind {
	case "reversed":
		owner = "back"
		in.Routes = append(in.Routes, Route{ID: owner, From: "B", To: "A", Orthogonal: true})
	case "loop":
		in.Boxes = in.Boxes[:1]
		in.Routes[0].To = "A"
	}
	in.Labels = []Label{{ID: "first.label", Owner: owner, Text: "one"}, {ID: "second.label", Owner: owner, Text: "longer"}}
	return in, owner
}

func assertLabelStack(t *testing.T, s scene.Scene, owner string) {
	t.Helper()
	var labels []scene.Label
	for _, label := range s.Labels {
		if label.Owner == owner {
			labels = append(labels, label)
		}
	}
	if len(labels) != 2 {
		t.Fatal("stack lost label identity", labels)
	}
	assertStackMembers(t, labels)
	if labels[1].Rect.Y-labels[0].Rect.Y != 2 {
		t.Fatal("one-cell text height plus one-cell slot gap", labels)
	}
}

func assertStackMembers(t *testing.T, labels []scene.Label) {
	t.Helper()
	if labels[0].ID != "first.label" || labels[1].ID != "second.label" {
		t.Fatal("stack declaration order changed", labels)
	}
	if labels[0].Rect.W != 3 || labels[1].Rect.W != 6 {
		t.Fatal("individual widths replaced by aggregate width", labels)
	}
	if labels[0].Rect.H != 1 || labels[1].Rect.H != 1 {
		t.Fatal("individual heights replaced by aggregate height", labels)
	}
}
