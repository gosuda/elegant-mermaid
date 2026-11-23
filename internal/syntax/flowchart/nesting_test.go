package flowchart

import (
	"fmt"
	"strings"
	"testing"
)

func TestSubgraphDepthRecovery(t *testing.T) {
	cases := []struct {
		name string
		body string
	}{
		{
			name: "opening keyword in heading",
			body: `subgraph hidden subgraph
Hidden["subgraph end"]
Hidden -->|end subgraph| Other
end
`,
		},
		{
			name: "closing keyword in heading",
			body: "subgraph other end\nOtherNode\nend\n",
		},
		{
			name: "adjacent bracketed headings",
			body: "subgraph bracketed[Title] subgraph child[Title]\nSkipped\nend\nend\n",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			file, diagnostics := Parse(subgraphDepthRecoverySource(tc.body), nil)
			if len(diagnostics) != 1 || diagnostics[0].Code != "limit/nesting-depth" {
				t.Fatalf("want one nesting error, got %+v", diagnostics)
			}
			requireDepthRecoveryTree(t, file.Doc.Lines)
		})
	}
}

func subgraphDepthRecoverySource(body string) []byte {
	var source strings.Builder
	source.WriteString("flowchart LR\n")
	for level := range 64 {
		fmt.Fprintf(&source, "subgraph S%d\n", level)
	}
	source.WriteString("subgraph overflow\n")
	source.WriteString(body)
	source.WriteString("end\nVisible\n")
	source.WriteString(strings.Repeat("end\n", 64))
	source.WriteString("After\n")
	return []byte(source.String())
}

func requireDepthRecoveryTree(t *testing.T, lines []Line) {
	t.Helper()
	if len(lines) != 2 {
		t.Fatalf("root statements: %d", len(lines))
	}
	requireDepthRecoveryNode(t, lines[1], "After")
	for range 64 {
		group := lines[0].Stmt.(*Subgraph)
		if len(group.Body) == 0 {
			t.Fatalf("missing ancestor group: %+v", lines[0])
		}
		lines = group.Body
	}
	if len(lines) != 2 {
		t.Fatalf("parent statements: %d", len(lines))
	}
	group := lines[0].Stmt.(*Subgraph)
	if len(group.Body) != 0 {
		t.Fatalf("overflowing subtree was parsed: %+v", lines[0])
	}
	requireDepthRecoveryNode(t, lines[1], "Visible")
}

func requireDepthRecoveryNode(t *testing.T, line Line, want string) {
	t.Helper()
	statement, ok := line.Stmt.(*VertexStatement)
	if !ok || len(statement.Groups) != 1 || len(statement.Groups[0].Vertices) != 1 {
		t.Fatalf("want one vertex, got %+v", line)
	}
	if got := statement.Groups[0].Vertices[0].Vertex.ID.String(); got != want {
		t.Fatalf("vertex %q; want %q", got, want)
	}
}
