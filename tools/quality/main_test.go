package main

import (
	"encoding/json"
	"math"
	"strings"
	"testing"
)

func TestExceptionThreshold(t *testing.T) {
	for _, tc := range []struct {
		ours, best int64
		want       bool
	}{{120, 100, false}, {121, 100, true}, {0, 0, false}, {1, 0, true}, {math.MaxInt64, math.MaxInt64, false}} {
		f := fixture{Ours: metric{Cost: tc.ours}, Dagre: metric{Cost: tc.best}, ELK: metric{Cost: tc.best}}
		if got := isException(f); got != tc.want {
			t.Errorf("ours=%d best=%d: got %t want %t", tc.ours, tc.best, got, tc.want)
		}
	}
}

func TestExceptionPercentage(t *testing.T) {
	for _, tc := range []struct {
		count int
		want  bool
	}{{20, true}, {19, false}} {
		fixtures := make([]fixture, tc.count)
		for i := range fixtures {
			fixtures[i] = fixture{Ours: metric{HardOK: true, Cost: 100}, Dagre: metric{Cost: 100}, ELK: metric{Cost: 100}}
		}
		fixtures[0].Ours.Cost = 121
		if got := evaluate(fixtures)[3]; got != tc.want {
			t.Errorf("1/%d: got %t want %t", tc.count, got, tc.want)
		}
	}
}

func TestBestBaseline(t *testing.T) {
	for _, tc := range []struct {
		dagre, elk int64
		want       string
	}{{10, 10, "dagre"}, {9, 10, "dagre"}, {10, 9, "elk"}} {
		name, _ := bestBaseline(fixture{Dagre: metric{Cost: tc.dagre}, ELK: metric{Cost: tc.elk}})
		if name != tc.want {
			t.Errorf("%d/%d: %s", tc.dagre, tc.elk, name)
		}
	}
}

func TestExceptionJSON(t *testing.T) {
	f := fixture{Path: "corpus/a&b.mmd", Ours: metric{Crossings: 2, Cost: 121}, Dagre: metric{Crossings: 1, Cost: 100}, ELK: metric{Crossings: 3, Cost: 110}}
	for _, tc := range []struct {
		name     string
		fixtures []fixture
		want     string
	}{
		{"empty", nil, "{\"schema\":1,\"fixtures\":0,\"exceptions\":[]}\n"},
		{"one", []fixture{f}, "{\"schema\":1,\"fixtures\":1,\"exceptions\":[{\"path\":\"corpus/a&b.mmd\",\"best\":\"dagre\",\"best_soft_cost\":100,\"ours\":{\"crossings\":2,\"soft_cost\":121},\"dagre\":{\"crossings\":1,\"soft_cost\":100},\"elk\":{\"crossings\":3,\"soft_cost\":110}}]}\n"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			got, err := exceptionBytes(tc.fixtures)
			if err != nil {
				t.Fatal(err)
			}
			if string(got) != tc.want {
				t.Errorf("got %s want %s", got, tc.want)
			}
		})
	}
}

func TestExceptionSort(t *testing.T) {
	fixtures := []fixture{{Path: "z", Ours: metric{Cost: 1}}, {Path: "a", Ours: metric{Cost: 1}}}
	data, err := exceptionBytes(fixtures)
	if err != nil {
		t.Fatal(err)
	}
	var r report
	if err := json.Unmarshal(data, &r); err != nil {
		t.Fatal(err)
	}
	if r.Exceptions[0].Path != "a" || r.Exceptions[1].Path != "z" {
		t.Fatalf("unsorted: %s", data)
	}
}

func TestGateTotals(t *testing.T) {
	for _, tc := range []struct {
		name string
		f    fixture
		want [4]bool
	}{
		{"equal", fixture{Ours: metric{HardOK: true, Cost: 10, Crossings: 2}, Dagre: metric{Cost: 10, Crossings: 2}, ELK: metric{Cost: 10, Crossings: 2}}, [4]bool{true, true, true, true}},
		{"elk worse", fixture{Ours: metric{Cost: 11, Crossings: 2}, Dagre: metric{Cost: 12, Crossings: 3}, ELK: metric{Cost: 10, Crossings: 1}}, [4]bool{false, false, false, true}},
	} {
		if got := evaluate([]fixture{tc.f}); got != tc.want {
			t.Errorf("%s got %v want %v", tc.name, got, tc.want)
		}
	}
}

func TestMetricValidation(t *testing.T) {
	valid := `{"schema":1,"hard_ok":false,"nodes":0,"mean_node_extent":1,"crossings":0,"bends":0,"against_flow_edges":0,"total_route_length":0,"canvas_area":0,"soft_cost":0}`
	if _, err := decodeMetric([]byte(valid)); err != nil {
		t.Fatal(err)
	}
	for _, bad := range []string{`{}`, strings.Replace(valid, `"soft_cost":0`, `"soft_cost":null`, 1), strings.Replace(valid, `"soft_cost":0`, `"soft_cost":-1`, 1), valid + valid} {
		if _, err := decodeMetric([]byte(bad)); err == nil {
			t.Errorf("accepted %s", bad)
		}
	}
}
