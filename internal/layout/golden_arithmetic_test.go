package layout

import (
	"encoding/json"
	"os"
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
)

type arithmeticGolden struct {
	Canvas geom.Size
	Boxes  []struct {
		ID         string
		X, Y, W, H int32
	}
	Routes []struct{ Points [][2]int32 }
}

func TestTwoNodeGoldenArithmetic(t *testing.T) {
	data, err := os.ReadFile("../../spec/golden/two-node.layout.json")
	if err != nil {
		t.Fatal(err)
	}
	var golden arithmeticGolden
	if err = json.Unmarshal(data, &golden); err != nil {
		t.Fatal(err)
	}
	if len(golden.Boxes) != 2 || len(golden.Routes) != 1 {
		t.Fatal("golden must hold two nodes and one route")
	}
	a, b := labelAdvanceWidth(t, "A"), labelAdvanceWidth(t, "B")
	padding := 2*goldenConstant(t, "node_pad_x") + 2*goldenConstant(t, "node_border")
	wa, wb := a+padding, b+padding
	h := goldenConstant(t, "line_h") + 2*goldenConstant(t, "node_pad_y") + 2*goldenConstant(t, "node_border")
	center := max(wa/2, wb/2)
	gap := goldenConstant(t, "rank_gap")
	secondY := h + gap
	expected := [][4]int32{{center - wa/2, 0, wa, h}, {center - wb/2, secondY, wb, h}}
	assertGoldenBoxes(t, golden, expected)
	if golden.Canvas != (geom.Size{W: wa, H: secondY + h}) {
		t.Fatalf("canvas: %v; expected %d x %d", golden.Canvas, wa, secondY+h)
	}
	points := [][2]int32{{center, h}, {center, secondY}}
	if !slices.Equal(golden.Routes[0].Points, points) {
		t.Fatalf("route: %v; expected %v", golden.Routes[0].Points, points)
	}
}

func assertGoldenBoxes(t *testing.T, golden arithmeticGolden, expected [][4]int32) {
	t.Helper()
	for i, box := range golden.Boxes {
		got := [4]int32{box.X, box.Y, box.W, box.H}
		if got != expected[i] {
			t.Fatalf("box %s: %v; expected %v", box.ID, got, expected[i])
		}
	}
}

func labelAdvanceWidth(t *testing.T, text string) int32 {
	t.Helper()
	width, err := measure.VectorWidth(text, 14, measure.WeightSemiBold)
	if err != nil {
		t.Fatal(err)
	}
	return width
}

func goldenConstant(t *testing.T, name string) int32 {
	t.Helper()
	for _, constant := range gen.LayoutConst {
		if constant.Name == "vector."+name {
			return constant.Value
		}
	}
	t.Fatalf("missing vector constant %s", name)
	return 0
}
