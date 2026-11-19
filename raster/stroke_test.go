package raster

import (
	"reflect"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestStrokeHorizontal(t *testing.T) {
	got := segmentOutline(point{10, 20}, point{110, 20}, 8)
	want := []point{{10, 16}, {110, 16}, {110, 24}, {10, 24}}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("segment quadrilateral %v, want %v", got, want)
	}
	cap := capOutline(point{10, 20}, 8)
	for i, want := range map[int]point{0: {14, 20}, 4: {10, 24}, 8: {6, 20}, 12: {10, 16}} {
		if cap[i] != want {
			t.Fatalf("cap vertex %d: %v, want %v", i, cap[i], want)
		}
	}
}

func TestStrokeDashes(t *testing.T) {
	path := contour{points: []point{{0, 0}, {100, 0}, {500, 0}}}
	got := dashRuns(path, scene.LineDotted)
	want := [][]point{{{0, 0}, {100, 0}, {192, 0}}, {{384, 0}, {500, 0}}}
	if !reflect.DeepEqual(got, want) {
		t.Fatalf("dash continuity %v, want %v", got, want)
	}
}
