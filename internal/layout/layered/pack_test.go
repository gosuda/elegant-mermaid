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
