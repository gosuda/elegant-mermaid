package layered

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestLabelNodes(t *testing.T) {
	g := &Graph{Nodes: []Node{{Decl: 0}, {Decl: 1}}, Edges: []Edge{{Tail: 0, Head: 1, MinLen: 2, Label: &EdgeLabel{W: 7, H: 3, Items: []MeasuredLabel{{ID: "label", W: 7, H: 3}}}}}, Params: Params{Slot: 1}}
	p, err := Normalize(g, []int32{0, 5})
	if err != nil {
		t.Fatal(err)
	}
	label := p.Nodes[p.Chains[0][2]]
	if label.Label == nil || label.W != 7 || label.H != 3 || p.Rank[p.Chains[0][2]] != 2 {
		t.Fatal("floor(5/2) midpoint replacement", p)
	}
	if len(p.Nodes) != 6 || len(p.Edges) != 5 {
		t.Fatal("label must replace, not append, a chain node", p)
	}
}

func TestCellLabelReservationArea(t *testing.T) {
	params, err := DefaultParams(scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	g := &Graph{Nodes: []Node{{Decl: 0}, {Decl: 1}}, Edges: []Edge{{Tail: 0, Head: 1, MinLen: 2, Label: &EdgeLabel{W: 3, H: 1, Items: []MeasuredLabel{{ID: "label", W: 3, H: 1}}}}}, Params: params}
	p, err := Normalize(g, []int32{0, 2})
	if err != nil {
		t.Fatal(err)
	}
	labels, err := placedLabels(p, []int32{0, 0, 0}, []int32{0, 12, 7})
	if err != nil {
		t.Fatal(err)
	}
	if labels.boxes[0].Rect != (geom.Rect{X: -1, Y: 7, W: 3, H: 1}) {
		t.Fatal("text must exclude the leading cell gutter", labels)
	}
	area, err := itemArea(Layout{Labels: labels.boxes, LabelReservations: labels.reservations})
	if err != nil {
		t.Fatal(err)
	}
	if area != 4 {
		t.Fatalf("reserved4x1 replaces text3x1 once, got %d", area)
	}
}

func TestLabelStackEnvelope(t *testing.T) {
	params, err := DefaultParams(scene.ProfileCell)
	if err != nil {
		t.Fatal(err)
	}
	aggregate := &EdgeLabel{W: 6, H: 3, Items: []MeasuredLabel{{ID: "one", W: 3, H: 1}, {ID: "longer", W: 6, H: 1}}}
	g := &Graph{Nodes: []Node{{Decl: 0}, {Decl: 1}}, Edges: []Edge{{Tail: 0, Head: 1, MinLen: 2, Label: aggregate}}, Params: params}
	p, err := Normalize(g, []int32{0, 2})
	if err != nil {
		t.Fatal(err)
	}
	labels, err := placedLabels(p, []int32{0, 0, 0}, []int32{0, 12, 7})
	if err != nil {
		t.Fatal(err)
	}
	if labels.boxes[0].Rect != (geom.Rect{X: -2, Y: 7, W: 3, H: 1}) || labels.boxes[1].Rect != (geom.Rect{X: -2, Y: 9, W: 6, H: 1}) {
		t.Fatal(labels)
	}
	area, err := itemArea(Layout{Labels: labels.boxes, LabelReservations: labels.reservations})
	if err != nil {
		t.Fatal(err)
	}
	if area != 21 {
		t.Fatalf("one reserved7x3 stack, not individual9+reserved21: %d", area)
	}
}
