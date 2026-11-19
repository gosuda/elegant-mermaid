package layered

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func TestPacking(t *testing.T) {
	parts := []Layout{
		{Boxes: []Box{{ID: "A", Rect: geom.Rect{X: -3, Y: -2, W: 5, H: 3}}}},
		{Boxes: []Box{{ID: "B", Rect: geom.Rect{X: 9, Y: 7, W: 4, H: 2}}}},
	}
	packed, err := Pack(parts, PackOptions{MaxWidth: 10, Gap: 2, AspectNum: 2, AspectDen: 1})
	if err != nil {
		t.Fatal(err)
	}
	if packed.Boxes[0].Rect != (geom.Rect{W: 5, H: 3}) || packed.Boxes[1].Rect != (geom.Rect{Y: 5, W: 4, H: 2}) || packed.Width != 5 || packed.Height != 7 {
		t.Fatal(packed)
	}
	area, err := itemArea(Layout{Boxes: []Box{{Rect: geom.Rect{W: 5, H: 3}}}, Extents: []Box{{Rect: geom.Rect{W: 2, H: 2}}}})
	if err != nil {
		t.Fatal(err)
	}
	if area != 19 {
		t.Fatal("loop reservation must contribute once", area)
	}
}

func squareParts(n int) []Layout {
	parts := make([]Layout, n)
	for i := range parts {
		parts[i] = Layout{Boxes: []Box{{ID: string(rune('A' + i)), Rect: geom.Rect{W: 10, H: 10}}}}
	}
	return parts
}

func TestPackingMinimisesPackedArea(t *testing.T) {
	opts := PackOptions{Gap: 2, AspectNum: 2, AspectDen: 1}
	target, err := packingTarget(squareParts(3), opts)
	if err != nil {
		t.Fatal(err)
	}
	if target != 10 {
		t.Fatal("the aspect target 24 packs 22 by 22; the first prefix sum 10 packs 10 by 34", target)
	}
	packed, err := Pack(squareParts(3), opts)
	if err != nil {
		t.Fatal(err)
	}
	if packed.Width != 10 || packed.Height != 34 {
		t.Fatal(packed.Width, packed.Height)
	}
}

func TestPackingTiesKeepAspectTarget(t *testing.T) {
	target, err := packingTarget(squareParts(2), PackOptions{Gap: 2, AspectNum: 2, AspectDen: 1})
	if err != nil {
		t.Fatal(err)
	}
	if target != 20 {
		t.Fatal("the prefix sums 10 and 22 pack to the same area 220 as the aspect target 20", target)
	}
}

func TestPackingMaxWidthSkipsAreaSearch(t *testing.T) {
	target, err := packingTarget(squareParts(3), PackOptions{MaxWidth: 24, Gap: 2, AspectNum: 2, AspectDen: 1})
	if err != nil {
		t.Fatal(err)
	}
	if target != 24 {
		t.Fatal(target)
	}
}
