package layout

import (
	"encoding/json"
	"os"
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type arithmeticGolden struct {
	Canvas geom.Size
	Boxes  []struct {
		ID         string
		X, Y, W, H int32
	}
	Routes []struct{ Points [][2]int32 }
	Labels []struct {
		ID, Owner, Text string
		X, Y, W, H      int32
		Lines           []string
	}
}
type goldenExpectations struct {
	canvas geom.Size
	boxes  [][4]int32
	route  [][2]int32
	label  [4]int32
}

func TestTwoNodeGoldenArithmetic(t *testing.T) {
	data, err := os.ReadFile("../../spec/golden/two-node.layout.json")
	if err != nil {
		t.Fatal(err)
	}
	var golden arithmeticGolden
	if err := json.Unmarshal(data, &golden); err != nil {
		t.Fatal(err)
	}
	if len(golden.Boxes) != 2 || len(golden.Routes) != 1 || len(golden.Labels) != 1 {
		t.Fatal("golden must hold two nodes, one route, one label")
	}
	expected := labelledGoldenArithmetic(t)
	assertGoldenBoxes(t, golden, expected.boxes)
	assertGoldenCanvas(t, golden, expected)
	assertGoldenRoute(t, golden, expected)
	assertGoldenLabel(t, golden, expected)
}
func labelledGoldenArithmetic(t *testing.T) goldenExpectations {
	t.Helper()
	a, b, label := labelAdvanceWidth(t, "A"), labelAdvanceWidth(t, "B"), labelAdvanceWidth(t, "yes")
	if a != 652 || b != 591 || label != 1550 {
		t.Fatalf("Inter 2048-upem arithmetic changed: %d %d %d", a, b, label)
	}
	padding := 2*goldenConstant(t, "node_pad_x") + 2*goldenConstant(t, "node_border")
	wa, wb := a+padding, b+padding
	lh := goldenConstant(t, "line_h")
	h := lh + 2*goldenConstant(t, "node_pad_y") + 2*goldenConstant(t, "node_border")
	slot, gap, margin := goldenConstant(t, "slot"), goldenConstant(t, "rank_gap"), goldenConstant(t, "canvas_margin")
	center := max(wa/2, wb/2, label/2) + margin
	labelTop := h + gap + slot
	targetTop := labelTop + lh + gap + slot
	left := center - label/2
	firstChannel := h + slot + slot/2 + margin
	secondChannel := labelTop + lh + slot + slot/2 + margin
	return goldenExpectations{
		canvas: geom.Size{W: wa + 2*margin, H: targetTop + h + 2*margin},
		boxes:  [][4]int32{{center - wa/2, margin, wa, h}, {center - wb/2, targetTop + margin, wb, h}},
		label:  [4]int32{left, labelTop + margin, label, lh},
		route:  [][2]int32{{center, h + margin}, {center, firstChannel}, {left, firstChannel}, {left, labelTop + margin}, {left, labelTop + lh + margin}, {left, secondChannel}, {center, secondChannel}, {center, targetTop + margin}},
	}
}
func assertGoldenCanvas(t *testing.T, golden arithmeticGolden, expected goldenExpectations) {
	t.Helper()
	if golden.Canvas != expected.canvas {
		t.Fatalf("canvas %v; expected %v", golden.Canvas, expected.canvas)
	}
}
func assertGoldenRoute(t *testing.T, golden arithmeticGolden, expected goldenExpectations) {
	t.Helper()
	if !slices.Equal(golden.Routes[0].Points, expected.route) {
		t.Fatalf("route %v; expected %v", golden.Routes[0].Points, expected.route)
	}
}
func assertGoldenLabel(t *testing.T, golden arithmeticGolden, expected goldenExpectations) {
	t.Helper()
	label := golden.Labels[0]
	if [4]int32{label.X, label.Y, label.W, label.H} != expected.label {
		t.Fatal("midpoint label box", label, expected.label)
	}
	if label.Text != "yes" || !slices.Equal(label.Lines, []string{"yes"}) {
		t.Fatal("label text or wrapped lines", label)
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
	var sum int64
	for _, r := range text {
		sum += goldenAdvance(t, r)
	}
	upem := int64(gen.AdvancesUpem[1])
	return int32((sum*14*64 + upem - 1) / upem)
}
func goldenAdvance(t *testing.T, r rune) int64 {
	t.Helper()
	for _, row := range gen.Advances {
		if row.Weight == 1 && row.CP == uint32(r) {
			return int64(row.Units)
		}
	}
	t.Fatalf("golden glyph %q is missing", r)
	return 0
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
