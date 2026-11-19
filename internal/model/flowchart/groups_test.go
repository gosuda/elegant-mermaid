package flowchart

import (
	"testing"

	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func TestFirstSubgraphMembership(t *testing.T) {
	source := []byte("flowchart\nsubgraph Frontend\nAPI --> UI\nend\nsubgraph Backend\nAPI --> DB\nend\nsubgraph Frontend[Replacement]\nNEW\nend\n")
	ast, diagnostics := syn.Parse(source, nil)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	model, diagnostics := Resolve(source, ast)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	if len(model.Groups) != 2 {
		t.Fatalf("groups: %+v", model.Groups)
	}
	for _, tc := range []struct {
		index   int
		title   string
		members []string
	}{{0, "Frontend", []string{"API", "UI", "NEW"}}, {1, "Backend", []string{"DB"}}} {
		g := model.Groups[tc.index]
		if g.Title != tc.title || len(g.Members) != len(tc.members) {
			t.Fatalf("group: %+v", g)
		}
		for i, want := range tc.members {
			if g.Members[i] != want {
				t.Fatalf("group: %+v", g)
			}
		}
	}
}

func TestNestedSubgraphCompletesFirst(t *testing.T) {
	source := []byte("flowchart\nsubgraph Outer\nA\nsubgraph Inner\nA\nend\nB\nend\n")
	ast, diagnostics := syn.Parse(source, nil)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	model, diagnostics := Resolve(source, ast)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	if len(model.Groups) != 2 || len(model.Groups[0].Members) != 1 || model.Groups[0].Members[0] != "B" || len(model.Groups[1].Members) != 1 || model.Groups[1].Members[0] != "A" {
		t.Fatalf("%+v", model.Groups)
	}
}

func TestTitleOnlySubgraphIDs(t *testing.T) {
	src := []byte("flowchart\nsubgraph S\nA\nend\nsubgraph S\nB\nend\nsubgraph \"Quoted group\"\nC\nend\n")
	ast, diagnostics := syn.Parse(src, nil)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	model, diagnostics := Resolve(src, ast)
	if len(diagnostics) != 0 {
		t.Fatal(diagnostics)
	}
	if len(model.Groups) != 2 || model.Groups[1].ID != "subGraph2" || model.Groups[1].Title != "Quoted group" {
		t.Fatalf("%+v", model.Groups)
	}
}
