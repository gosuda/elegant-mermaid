package raster

import (
	"image"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
)

type interval struct {
	x0, x1 int64
	empty  bool
}

func TestFallbackMixedLabelHasInk(t *testing.T) {
	outlines := InterOutlines()
	data, ok := scenelink.OutlinesOf(outlines)
	if !ok {
		t.Fatal("no outlines")
	}
	label := &scene.Text{Rect: geom.Rect{X: 640, Y: 640, W: 30000, H: 2560}, Size: 32, Role: scene.TextRoleBody, Style: "text", Lines: [][]scene.Run{{{Text: "中文 \U0001F600 \U0001D518 ⚗"}}}}
	s := scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 31280, H: 3840}}, Groups: []*scene.Group{{Items: []scene.Primitive{label}}}}
	enc, err := encodeScene(s, Options{Scale: 2})
	img := decoded(t, enc, err)
	if singleColour(img) {
		t.Fatal("want ink")
	}
	line := label.Lines[0]
	w := data.LineWidth(label, line)
	x := scenelink.TextLeft(label, w)
	y := scenelink.Baseline(label, 0)
	checked := 0
	for _, iv := range collectIntervals(data, label, line, x, y) {
		if iv.empty {
			continue
		}
		assertInkInSpan(t, img, iv)
		checked++
	}
	if checked < 4 {
		t.Fatalf("want at least four ink intervals, got %d", checked)
	}
}

func collectIntervals(data scenelink.Outlines, label *scene.Text, line []scene.Run, x, y int64) []interval {
	var out []interval
	for g, at := range data.Glyphs(label, line, x, y) {
		x0, x1 := inkSpan(g, at, label.Size)
		out = append(out, interval{x0: x0, x1: x1, empty: len(g.Commands) == 0})
	}
	return out
}

func inkSpan(g scenelink.Glyph, at scenelink.Placement, size int32) (int64, int64) {
	if at.Slot == 0 && at.Natural == 0 {
		adv := int64(g.Advance) * int64(size) * 64
		n := (2*adv + int64(at.UnitsPerEm)) / (2 * int64(at.UnitsPerEm))
		return at.X, at.X + n
	}
	if at.Natural > at.Slot {
		return at.X, at.X + at.Slot
	}
	return at.X, at.X + at.Natural
}

func assertInkInSpan(t *testing.T, img image.Image, iv interval) {
	t.Helper()
	x0p := int(iv.x0 * 2 / 64)
	x1p := int((iv.x1*2 + 63) / 64)
	if x1p <= x0p {
		t.Fatalf("empty pixel interval %d %d", x0p, x1p)
	}
	br, bg, bb, _ := img.At(0, 0).RGBA()
	for px := x0p; px < x1p; px++ {
		if px < 0 || px >= img.Bounds().Dx() {
			continue
		}
		if columnHasInk(img, px, br, bg, bb) {
			return
		}
	}
	t.Fatalf("no ink in interval %d %d", x0p, x1p)
}

func columnHasInk(img image.Image, px int, br, bg, bb uint32) bool {
	for py := 0; py < img.Bounds().Dy(); py++ {
		r, g, b, _ := img.At(px, py).RGBA()
		if r != br || g != bg || b != bb {
			return true
		}
	}
	return false
}
