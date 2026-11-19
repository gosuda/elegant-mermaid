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

func TestTypedShapeCanonicalID(t *testing.T) {
	for _, tc := range []struct{ source, shape string }{
		{"flowchart TD\nA@{ shape: diamond }\n", "diam"},
		{"flowchart TD\nA{choice}\n", "diamond"},
	} {
		src := []byte(tc.source)
		ast, diagnostics := syn.Parse(src, nil)
		if len(diagnostics) != 0 {
			t.Fatalf("syntax: %+v", diagnostics)
		}
		model, diagnostics := Resolve(src, ast)
		if len(diagnostics) != 0 || len(model.Nodes) != 1 || model.Nodes[0].Shape != tc.shape {
			t.Fatalf("model=%+v diagnostics=%+v; want %s", model, diagnostics, tc.shape)
		}
	}
}

func TestEdgeAttributeReference(t *testing.T) {
	src := []byte("flowchart LR\nA e1@--> B\ne1@{ animate: true, curve: basis }\n")
	ast, diagnostics := syn.Parse(src, nil)
	if len(diagnostics) != 0 {
		t.Fatalf("syntax: %+v", diagnostics)
	}
	model, diagnostics := Resolve(src, ast)
	if len(diagnostics) != 0 || len(model.Nodes) != 2 || len(model.Edges) != 1 {
		t.Fatalf("model=%+v diagnostics=%+v", model, diagnostics)
	}
	edge := model.Edges[0]
	if edge.UserID != "e1" || edge.Attrs["animate"] != "true" || edge.Attrs["curve"] != "basis" {
		t.Fatalf("edge attributes: %+v", edge)
	}
}

func TestEdgeMarkers(t *testing.T) {
	for _, tc := range []struct{ link, start, end, stroke string }{
		{"<-->", "point", "point", "normal"},
		{"o--o", "circle", "circle", "normal"},
		{"x--x", "cross", "cross", "normal"},
		{"o--x", "none", "none", "normal"},
		{"<==>", "point", "point", "thick"},
		{"o==o", "circle", "circle", "thick"},
		{"x==x", "cross", "cross", "thick"},
		{"o==x", "none", "none", "thick"},
		{"<-.->", "point", "point", "dotted"},
		{"o-.-o", "circle", "circle", "dotted"},
		{"x-.-x", "cross", "cross", "dotted"},
		{"o-.-x", "none", "none", "dotted"},
		{"<-- text -->", "point", "point", "normal"},
		{"-- text -->", "none", "point", "normal"},
	} {
		src := []byte("flowchart LR\nA " + tc.link + " B\n")
		ast, diagnostics := syn.Parse(src, nil)
		if len(diagnostics) != 0 {
			t.Fatalf("%s: %+v", tc.link, diagnostics)
		}
		model, diagnostics := Resolve(src, ast)
		if len(diagnostics) != 0 || len(model.Edges) != 1 {
			t.Fatalf("%s: %+v %+v", tc.link, model, diagnostics)
		}
		edge := model.Edges[0]
		if edge.Start != tc.start || edge.Marker != tc.end || edge.Stroke != tc.stroke || edge.Length != 1 {
			t.Errorf("%s: %+v", tc.link, edge)
		}
	}
	_, diagnostics := syn.Parse([]byte("flowchart LR\nA <-- B\n"), nil)
	if len(diagnostics) == 0 {
		t.Fatal("accepted incomplete split link <--")
	}
}
