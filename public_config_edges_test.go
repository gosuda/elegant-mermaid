package mermaid_test

import (
	"fmt"
	"strings"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
)

type configEdgeCase struct {
	kind, source, statement string
	count, limit            int
}

func configEdgeFixtures() []configEdgeCase {
	return []configEdgeCase{
		{"flowchart", "flowchart LR\nA --> B\n", "A --> B", 1, 0},
		{"swimlane", "swimlane-beta LR\nA --> B\n", "A --> B", 1, 0},
		{"agentflow", "agentflow-beta TB\nA --> B\n", "A --> B", 1, 0},
		{"architecture", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\n", "a:R -- L:b", 1, 0},
		{"block", "block-beta\nA --> B\n", "A --> B", 1, 0},
		{"c4", "C4Context\nPerson(a, \"A\")\nPerson(b, \"B\")\nRel(a, b, \"link\")\n", "Rel(a, b, \"link\")", 1, 0},
		{"class", "classDiagram\nA --> B\n", "A --> B", 1, 0},
		{"cynefin", "cynefin-beta\ncomplex --> clear\n", "complex --> clear", 1, 0},
		{"er", "erDiagram\nA ||--o{ B : owns\n", "A ||--o{ B : owns", 1, 0},
		{"requirement", "requirementDiagram\nrequirement A {\n}\nelement B {\n}\nA - satisfies -> B\n", "A - satisfies -> B", 1, 0},
		{"sankey", "sankey\nA,B,1\n", "A,B,1", 1, 0},
		{"state", "stateDiagram-v2\nA --> B\n", "A --> B", 1, 0},
		{"usecase", "usecase-beta\nactor A\nU(Task)\nA --> U\n", "A --> U", 1, 0},
		{"wardley", "wardley-beta\ncomponent A [0.1, 0.2]\ncomponent B [0.3, 0.4]\nA -> B\n", "A -> B", 1, 0},
		{"eventmodeling", "eventmodeling\ntf 01 cmd Add\ntf 02 evt Added\n", "tf 02 evt Added", 1, 0},
		{"gitgraph", "gitGraph\ncommit id: \"A\"\nbranch develop\ncommit id: \"B\"\ncheckout main\ncommit id: \"C\"\nmerge develop\ncherry-pick id: \"B\"\n", "cherry-pick id: \"B\"", 6, 5},
		{"ishikawa", "ishikawa-beta\nRoot\n  Child\n", "Child", 1, 0},
		{"mindmap", "mindmap\nRoot\n  Child\n", "Child", 1, 0},
		{"treeview", "treeView-beta\nRoot\n  Child\n", "  Child", 2, 1},
		{"sequence", "sequenceDiagram\nA->>B: hello\n", "A->>B: hello", 1, 0},
	}
}

func TestPublicConfigSemanticEdgeStatements(t *testing.T) {
	for _, tc := range configEdgeFixtures() {
		t.Run(tc.kind, func(t *testing.T) {
			source := fmt.Sprintf("---\nconfig:\n  maxEdges: %d\n---\n%s", tc.limit, tc.source)
			document := mermaid.Parse([]byte(source))
			diagnostic := requireConfigDiagnostic(t, document, "limit/max-edges")
			assertOnlyConfigEdgeError(t, document)
			start := strings.Index(source, tc.statement)
			want := mermaid.Span{Start: start, End: start + len(tc.statement)}
			if diagnostic.Span != want || diagnostic.Message != fmt.Sprintf("diagram has %d edges; the limit is %d", tc.count, tc.limit) {
				t.Fatalf("semantic edge: %+v, want span %+v and count %d", diagnostic, want, tc.count)
			}
		})
	}
}

func assertOnlyConfigEdgeError(t *testing.T, document *mermaid.Document) {
	t.Helper()
	for _, diagnostic := range document.Diagnostics() {
		if diagnostic.Severity == mermaid.SeverityError && diagnostic.Code != "limit/max-edges" {
			t.Fatalf("invalid edge fixture: %+v", diagnostic)
		}
	}
}
