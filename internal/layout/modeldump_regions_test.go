package layout

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestModelDumpRegionsAndNodeDirection(t *testing.T) {
	in := Input{
		Kind:    "sequence",
		Profile: scene.ProfileVector,
		Boxes: []Box{
			{ID: "box0", Role: scene.RoleGroup, Direction: "w", Text: "team"},
			{ID: "A", Role: scene.RoleNode, Parent: "box0", Exclusive: true, Direction: "n", Text: "Alice"},
			{ID: "B", Role: scene.RoleNode, Exclusive: true},
		},
		RegionSets: []layered.RegionSet{{Parent: 0, Regions: []int{0, 1, 2, -1}}, {Parent: 1, Regions: []int{5, 0}}},
	}
	got := string(dumpInput(t, in))
	for _, want := range []string{
		`{"id":"box0","role":"group","parent":"","exclusive":false,"direction":"w","text":"team"}`,
		`{"id":"A","role":"node","parent":"box0","exclusive":true,"direction":"n","text":"Alice"}`,
		`{"id":"B","role":"node","parent":"","exclusive":true}`,
		"\n\"regions\":[[0,0,1,2,-1],\n[1,5,0]]}\n",
	} {
		if !strings.Contains(got, want) {
			t.Fatalf("missing %q in %s", want, got)
		}
	}
}

func TestModelDumpOmitsEmptyRegionsAndNodeDirection(t *testing.T) {
	in := Input{
		Kind:    "flowchart",
		Profile: scene.ProfileVector,
		Boxes: []Box{
			{ID: "g", Role: scene.RoleGroup},
			{ID: "A", Role: scene.RoleNode, Parent: "g", Exclusive: true},
		},
	}
	got := string(dumpInput(t, in))
	if strings.Contains(got, `"regions"`) {
		t.Fatalf("regions written for an input with no region set: %s", got)
	}
	if !strings.Contains(got, `{"id":"A","role":"node","parent":"g","exclusive":true}`) {
		t.Fatalf("node box carries extra keys: %s", got)
	}
	if !strings.Contains(got, `{"id":"g","role":"group","parent":"","exclusive":false,"direction":""}`) {
		t.Fatalf("group box lost its direction key: %s", got)
	}
}
