package tui

import (
	"image"
	"image/color"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
)

func TestCompositeNearestNeighbourAndPan(t *testing.T) {
	src := image.NewRGBA(image.Rect(0, 0, 6, 4))
	for y := range 4 {
		for x := range 6 {
			src.SetRGBA(x, y, color.RGBA{R: uint8(20 * x), G: uint8(30 * y), B: 17, A: 255})
		}
	}
	state := New("diagram.mmd", "elegant-light")
	state.Mode = termgfx.ModeKitty
	state.Pixels = src
	state.Width = 3
	state.Height = 4
	state.CellW = 1
	state.CellH = 1
	state.Zoom = 150
	state.Fit = false
	state.OffsetX = 2
	state.OffsetY = 1
	got, err := composite(state)
	if err != nil {
		t.Fatal(err)
	}
	for y := range 2 {
		for x := range 3 {
			want := src.RGBAAt((x+2)*2/3, (y+1)*2/3)
			if got.RGBAAt(x, y) != want {
				t.Fatalf("pixel %d,%d: got %v want %v", x, y, got.RGBAAt(x, y), want)
			}
		}
	}
	for _, viewport := range []struct {
		height, offsetY int
	}{{5, 1}, {8, 0}} {
		state.Resize(20, viewport.height)
		if state.OffsetX != 0 || state.OffsetY != viewport.offsetY {
			t.Fatalf("height %d must preserve the centre and clamp offsets: got %d,%d want 0,%d", viewport.height, state.OffsetX, state.OffsetY, viewport.offsetY)
		}
	}
}

func TestFrameControlBytesNeverReachTerminal(t *testing.T) {
	state := New("evil\x1b[2J\rname.mmd", "elegant-light")
	state.Diagnostics = []string{"error bad\x1b[2J 1:1 text"}
	state.Panel = "diagnostics"
	frame := Frame(state)
	for _, r := range frame {
		if r == 27 || r == '\r' {
			t.Fatalf("unescaped control %U", r)
		}
	}
}
