package flowchart

import (
	"fmt"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type depthRecoveryDiagnostic struct {
	code string
	span source.Span
}

func TestSubgraphDepthRecovery(t *testing.T) {
	cases := []struct {
		name       string
		body       string
		diagnostic depthRecoveryDiagnostic
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
		{
			name:       "malformed line ignores opening keyword",
			body:       "[junk] subgraph fake\n",
			diagnostic: depthRecoveryDiagnostic{codeUnknownStatement, source.Span{Start: 0, End: 20}},
		},
		{
			name:       "malformed line ignores closing keyword",
			body:       "[junk] end\n",
			diagnostic: depthRecoveryDiagnostic{codeUnknownStatement, source.Span{Start: 0, End: 10}},
		},
		{
			name:       "vertex tail ignores opening keyword",
			body:       "Node subgraph fake\n",
			diagnostic: depthRecoveryDiagnostic{codeUnexpectedToken, source.Span{Start: 5, End: 13}},
		},
		{
			name:       "malformed line recovers at semicolon",
			body:       "[junk] subgraph fake; subgraph nested[Title]\nHidden\nend\n",
			diagnostic: depthRecoveryDiagnostic{codeUnknownStatement, source.Span{Start: 0, End: 20}},
		},
		{
			name: "directive before same-line subgraph",
			body: "style Hidden fill:red subgraph nested[Title]\nHidden\nend\n",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			input := subgraphDepthRecoverySource(tc.body)
			file, diagnostics := Parse(input, nil)
			requireDepthRecoveryDiagnostics(t, input, diagnostics, tc.diagnostic)
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

func requireDepthRecoveryDiagnostics(t *testing.T, input []byte, diagnostics []diag.Diagnostic, want depthRecoveryDiagnostic) {
	t.Helper()
	count := 1
	if want.code != "" {
		count++
	}
	if len(diagnostics) != count || diagnostics[0].Code != "limit/nesting-depth" {
		t.Fatalf("want nesting error and %+v, got %+v", want, diagnostics)
	}
	if want.code == "" {
		return
	}
	const header = "subgraph overflow\n"
	start := strings.Index(string(input), header) + len(header)
	want.span.Start += start
	want.span.End += start
	if got := diagnostics[1]; got.Code != want.code || got.Span != want.span {
		t.Fatalf("want body diagnostic %+v, got %+v", want, got)
	}
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
