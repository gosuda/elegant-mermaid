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
