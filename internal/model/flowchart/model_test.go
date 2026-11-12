package flowchart

import (
	"testing"

	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func TestResolveDemo(t *testing.T) {
	for _, src := range []string{"flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n", "flowchart LR\n  A[Start --> B\n"} {
		ast, ds := syn.Parse([]byte(src), nil)
		m, semantic := Resolve([]byte(src), ast)
		t.Logf("diagnostics=%+v semantic=%+v nodes=%+v edges=%+v", ds, semantic, m.Nodes, m.Edges)
		if len(ds) == 0 && (len(m.Nodes) != 3 || len(m.Edges) != 3) {
			t.Fatalf("unexpected demo model: %+v", m)
		}
	}
}

func TestTypedShapeValueSpan(t *testing.T) {
	src := []byte("flowchart\nA@{ shape: missing }\n")
	ast, syntax := syn.Parse(src, nil)
	if len(syntax) != 0 {
		t.Fatalf("syntax diagnostics: %+v", syntax)
	}
	_, diagnostics := Resolve(src, ast)
	if len(diagnostics) != 1 {
		t.Fatalf("diagnostics: %+v", diagnostics)
	}
	d := diagnostics[0]
	if d.Code != "flowchart/typed-shape-unsupported" || string(src[d.Span.Start:d.Span.End]) != "missing" {
		t.Fatalf("wrong typed shape diagnostic: %+v", d)
	}
}

func TestIncompleteEdgeDoesNotResolve(t *testing.T) {
	src := []byte("flowchart\nA -->\n")
	ast, diagnostics := syn.Parse(src, nil)
	if len(diagnostics) == 0 {
		t.Fatal("missing incomplete edge diagnostic")
	}
	model, _ := Resolve(src, ast)
	if len(model.Edges) != 0 {
		t.Fatalf("incomplete edge resolved: %+v", model.Edges)
	}
}
