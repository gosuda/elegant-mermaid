package scene

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func TestMetrics(t *testing.T) {
	tests := []struct {
		name string
		dump Dump
		want Metrics
	}{
		{"empty", Dump{}, Metrics{Schema: 1, HardOK: true, MeanNodeExtent: 1}},
		{"straight", Dump{Options: Options{Direction: DirectionLR}, Canvas: geom.Size{W: 30, H: 10}, Boxes: []Box{{ID: "a", Rect: geom.Rect{W: 10, H: 10}}, {ID: "b", Rect: geom.Rect{X: 20, W: 10, H: 10}}}, Routes: []Route{{ID: "e", From: "a", To: "b", Points: []geom.Point{{X: 10, Y: 5}, {X: 10, Y: 5}, {X: 20, Y: 5}}}}}, Metrics{Schema: 1, HardOK: true, Nodes: 2, MeanNodeExtent: 10, TotalRouteLength: 10, CanvasArea: 300, SoftCost: 2}},
		{"reversal", Dump{Canvas: geom.Size{W: 3}, Boxes: []Box{{ID: "a"}}, Routes: []Route{{ID: "e", From: "a", To: "a", Points: []geom.Point{{}, {X: 3}, {}}}}}, Metrics{Schema: 1, HardOK: true, Nodes: 1, MeanNodeExtent: 1, Bends: 1, TotalRouteLength: 6, SoftCost: 8}},
		{"diagonal crossing", Dump{Canvas: geom.Size{W: 10, H: 10}, Boxes: []Box{{ID: "a"}, {ID: "b", Rect: geom.Rect{X: 10, Y: 10}}, {ID: "c", Rect: geom.Rect{Y: 10}}, {ID: "d", Rect: geom.Rect{X: 10}}}, Routes: []Route{{ID: "e", From: "a", To: "b", Points: []geom.Point{{}, {X: 10, Y: 10}}}, {ID: "f", From: "c", To: "d", Points: []geom.Point{{Y: 10}, {X: 10}}}}}, Metrics{Schema: 1, HardOK: true, Nodes: 4, MeanNodeExtent: 1, Crossings: 1, AgainstFlowEdges: 1, TotalRouteLength: 28, CanvasArea: 100, SoftCost: 68}},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			got, err := MeasureMetrics(&tc.dump, 0)
			if err != nil {
				t.Fatal(err)
			}
			if got != tc.want {
				t.Fatalf("got %+v want %+v", got, tc.want)
			}
		})
	}
}
