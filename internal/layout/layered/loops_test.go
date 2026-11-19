package layered

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func TestSelfLoops(t *testing.T) {
	g := &Graph{Nodes: []Node{{ID: "A", W: 10, H: 3}}, Edges: []Edge{{Tail: 0, Head: 0, MinLen: 1, Label: &EdgeLabel{W: 7, H: 5, Items: []MeasuredLabel{{ID: "label", W: 7, H: 5}}}}, {Tail: 0, Head: 0, MinLen: 1, Decl: 1}}, Params: Params{Slot: 1}}
	if err := sizeLoops(g); err != nil {
		t.Fatal(err)
	}
	assertLoopSizing(t, g)
	boxes := []Box{{ID: "A", Rect: geom.Rect{X: 2, Y: 3, W: 10, H: 20}}}
	routes, err := Loops(g, boxes)
	if err != nil {
		t.Fatal(err)
	}
	if routes[0].Points[0] != (geom.Point{X: 12, Y: 4}) || routes[1].Points[2] != (geom.Point{X: 14, Y: 11}) {
		t.Fatal(routes)
	}
	labels, err := loopLabels(g, boxes)
	if err != nil {
		t.Fatal(err)
	}
	wantX := boxes[0].Rect.X + boxes[0].Rect.W + g.Slot*int32(len(g.Edges)+1)
	if labels.boxes[0].Rect != (geom.Rect{X: wantX, Y: 3, W: 7, H: 5}) {
		t.Fatal(labels)
	}
	extents, err := loopExtents(g, boxes)
	if err != nil {
		t.Fatal(err)
	}
	if extents[0].Rect != (geom.Rect{X: 12, Y: 3, W: 12, H: 10}) {
		t.Fatal(extents)
	}
}

func assertLoopSizing(t *testing.T, g *Graph) {
	t.Helper()
	if g.Nodes[0].H != 20 || g.Nodes[0].Extent != 12 {
		t.Fatalf("two five-unit bands require height20, extent(2+7)+(3+0)=12: %v", g.Nodes)
	}
}

func TestLoopLabelsShareOuterColumn(t *testing.T) {
	for _, frame := range []bool{false, true} {
		g := &Graph{
			Nodes: []Node{{ID: "A", W: 10, H: 20}},
			Edges: []Edge{
				{Tail: 0, Head: 0, MinLen: 1, Label: &EdgeLabel{W: 5, H: 3, Items: []MeasuredLabel{{ID: "one", W: 5, H: 1}, {ID: "extra", W: 3, H: 1}}}},
				{Tail: 0, Head: 0, MinLen: 1, Decl: 1, Label: &EdgeLabel{W: 3, H: 1, Items: []MeasuredLabel{{ID: "two", W: 3, H: 1}}}},
			},
			Params: Params{Slot: 1},
		}
		box := Box{ID: "A", Rect: geom.Rect{X: 2, Y: 3, W: 10, H: 20}}
		if frame {
			for i := range g.Edges {
				g.Edges[i].FrameLoop = "A"
			}
			g, _ = frameLoopGraph(g, "A", box)
		}
		assertLoopLabelOuterColumn(t, g, box)
	}
}

func assertLoopLabelOuterColumn(t *testing.T, g *Graph, box Box) {
	t.Helper()
	labels, err := loopLabels(g, []Box{box})
	if err != nil {
		t.Fatal(err)
	}
	wantX := box.Rect.X + box.Rect.W + g.Slot*int32(len(g.Edges)+1)
	if len(labels.boxes) != 3 || len(labels.reservations) != 2 {
		t.Fatal("stack labels or reservations lost", labels)
	}
	for i, id := range []string{"one", "extra", "two"} {
		if labels.boxes[i].ID != id || labels.boxes[i].Rect.X != wantX {
			t.Fatal("stack order or outer column", labels.boxes)
		}
	}
	for _, reservation := range labels.reservations {
		if reservation.Rect.X != wantX {
			t.Fatal("envelope did not follow its labels", labels.reservations)
		}
	}
}
