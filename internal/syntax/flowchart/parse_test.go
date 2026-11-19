package flowchart

import (
	"strings"
	"testing"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(t *testing.T, src string) (*File, []diag.Diagnostic) {
	t.Helper()
	return Parse([]byte(src), nil)
}

func codesOf(diags []diag.Diagnostic) []string {
	codes := make([]string, len(diags))
	for i := range diags {
		codes[i] = diags[i].Code
	}
	return codes
}

func TestParseHeader(t *testing.T) {
	cases := []struct {
		name    string
		src     string
		keyword string
		dir     string
		lines   int
	}{
		{"graph-tb", "graph TB\nA-->B\n", "graph", "TB", 1},
		{"flowchart-td", "flowchart TD\nA\n", "flowchart", "TD", 1},
		{"flowchart-elk", "flowchart-elk LR\nA\n", "flowchart-elk", "LR", 1},
		{"no-direction", "flowchart\nA\n", "flowchart", "", 1},
		{"br-keyword", "flowchart BR\nA\n", "flowchart", "BR", 1},
		{"semicolon-header", "flowchart LR;A-->B\n", "flowchart", "LR", 1},
		{"spaces-before", "\n\n  flowchart LR\nA\n", "flowchart", "LR", 1},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			file, diags := parse(t, tc.src)
			if len(diags) != 0 {
				t.Fatalf("diagnostics %v, want none", codesOf(diags))
			}
			if got := file.Config.Keyword.Text; got != tc.keyword {
				t.Fatalf("keyword %q, want %q", got, tc.keyword)
			}
			dir := headerDirection(file)
			if dir != tc.dir {
				t.Fatalf("direction %q, want %q", dir, tc.dir)
			}
			if len(file.Doc.Lines) != tc.lines {
				t.Fatalf("lines %d, want %d", len(file.Doc.Lines), tc.lines)
			}
		})
	}
}

func headerDirection(file *File) string {
	if file.Config.Direction == nil {
		return ""
	}
	return strings.TrimSpace(file.Config.Direction.Text)
}

func TestParseVertexShapes(t *testing.T) {
	cases := []struct {
		src   string
		shape string
		label string
	}{
		{"flowchart TD\nA[text]\n", "squareRect", "text"},
		{"flowchart TD\nA(text)\n", "roundedRect", "text"},
		{"flowchart TD\nA((text))\n", "circle", "text"},
		{"flowchart TD\nA(((text)))\n", "doublecircle", "text"},
		{"flowchart TD\nA([text])\n", "stadium", "text"},
		{"flowchart TD\nA[[text]]\n", "subroutine", "text"},
		{"flowchart TD\nA[(text)]\n", "cylinder", "text"},
		{"flowchart TD\nA{text}\n", "diamond", "text"},
		{"flowchart TD\nA>text]\n", "odd", "text"},
		{"flowchart TD\nA[/text\\]\n", "trapezoid", "text"},
		{"flowchart TD\nA[\\text/]\n", "inv_trapezoid", "text"},
		{"flowchart TD\nA(-text-)\n", "ellipse", "text"},
		{"flowchart TD\nA\n", "squareRect", ""},
	}
	for _, tc := range cases {
		file, diags := parse(t, tc.src)
		if len(diags) != 0 {
			t.Fatalf("%q: diagnostics %v", tc.src, codesOf(diags))
		}
		stmt, ok := file.Doc.Lines[0].Stmt.(*VertexStatement)
		if !ok {
			t.Fatalf("%q: statement is %T", tc.src, file.Doc.Lines[0].Stmt)
		}
		vertex := stmt.Groups[0].Vertices[0].Vertex
		if vertex.Shape != tc.shape {
			t.Fatalf("%q: shape %q, want %q", tc.src, vertex.Shape, tc.shape)
		}
		if got := vertex.Text.String(); got != tc.label {
			t.Fatalf("%q: label %q, want %q", tc.src, got, tc.label)
		}
	}
}

func TestParseLinks(t *testing.T) {
	cases := []struct {
		src   string
		edges int
		open  string
		end   string
		label string
	}{
		{"flowchart TD\nA --> B\n", 1, "", "-->", ""},
		{"flowchart TD\nA ==> B\n", 1, "", "==>", ""},
		{"flowchart TD\nA -.-> B\n", 1, "", "-.->", ""},
		{"flowchart TD\nA --- B\n", 1, "", "---", ""},
		{"flowchart TD\nA ~~~ B\n", 1, "", "~~~", ""},
		{"flowchart TD\nA -- text --> B\n", 1, "--", "-->", "text"},
		{"flowchart TD\nA -->|label| B\n", 1, "", "-->", "label"},
		{"flowchart TD\nA --> B --> C\n", 2, "", "-->", ""},
		{"flowchart TD\nA x--x B\n", 1, "", "x--x", ""},
	}
	for _, tc := range cases {
		t.Run(tc.src, func(t *testing.T) {
			file, diags := parse(t, tc.src)
			if len(diags) != 0 {
				t.Fatalf("%q: diagnostics %v", tc.src, codesOf(diags))
			}
			stmt := file.Doc.Lines[0].Stmt.(*VertexStatement)
			if len(stmt.Links) != tc.edges {
				t.Fatalf("%q: edges %d, want %d", tc.src, len(stmt.Links), tc.edges)
			}
			link := stmt.Links[0]
			checkLink(t, link, tc.open, tc.end, tc.label)
		})
	}
}

func checkLink(t *testing.T, link Link, wantOpen, wantEnd, wantLabel string) {
	t.Helper()
	open, end := "", link.Statement.Open.Text
	if link.Statement.End != nil {
		open = strings.TrimSpace(link.Statement.Open.Text)
		end = link.Statement.End.Text
	}
	if open != wantOpen || strings.TrimSpace(end) != wantEnd {
		t.Fatalf("link halves %q %q, want %q %q", open, end, wantOpen, wantEnd)
	}
	label := ""
	if link.Edge != nil {
		label = link.Edge.Text.String()
	}
	if link.Arrow != nil {
		label = link.Arrow.Text.String()
	}
	if label != wantLabel {
		t.Fatalf("label %q, want %q", label, wantLabel)
	}
}

func TestParseNodeGroup(t *testing.T) {
	file, diags := parse(t, "flowchart TD\nA & B & C --> D\n")
	if len(diags) != 0 {
		t.Fatalf("diagnostics %v", codesOf(diags))
	}
	stmt := file.Doc.Lines[0].Stmt.(*VertexStatement)
	if len(stmt.Groups) != 2 {
		t.Fatalf("groups %d, want 2", len(stmt.Groups))
	}
	if len(stmt.Groups[0].Vertices) != 3 {
		t.Fatalf("first group vertices %d, want 3", len(stmt.Groups[0].Vertices))
	}
}

func TestParseSubgraph(t *testing.T) {
	src := "flowchart TD\nsubgraph one [Title]\nA --> B\ndirection LR\nend\n"
	file, diags := parse(t, src)
	if len(diags) != 0 {
		t.Fatalf("diagnostics %v", codesOf(diags))
	}
	sg, ok := file.Doc.Lines[0].Stmt.(*Subgraph)
	if !ok {
		t.Fatalf("statement is %T", file.Doc.Lines[0].Stmt)
	}
	if sg.ID.String() != "one" {
		t.Fatalf("id %q", sg.ID.String())
	}
	if sg.Title.String() != "Title" {
		t.Fatalf("title %q", sg.Title.String())
	}
	if len(sg.Body) != 2 {
		t.Fatalf("body %d, want 2", len(sg.Body))
	}
	if sg.Direction == nil {
		t.Fatal("direction missing")
	}
}

func TestSpanBoundsAndRuneBoundaries(t *testing.T) {
	sources := []string{
		"flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n",
		"flowchart TD\nsubgraph s1\nA[é] --> B[日本]\nend\n",
		"flowchart TD\nA @@@ B\n",
		"flowchart TD\nA[\"unclosed\n",
		"flowchart TD\nA[[nested]] --> B(((x)))\n",
		"flowchart TD\nstyle A fill:#f9f\nclassDef c fill:#f00\nclass A c\n",
		"flowchart TD\nclick A \"https://example.com\" \"tip\" _blank\n",
		"flowchart TD\naccTitle: title text\naccDescr: description\n",
		"flowchart TD\nA@{ shape: rect, label: \"hello\" }\n",
		"flowchart TD\nlinkStyle default interpolate basis stroke:#f00\n",
		"flowchart TD\nA[\"multi\nline\"]\n",
		"flowchart TD\nsubgraph\nend\n",
		"flowchart TD\n%%{init: {}}%%\nA-->B\n",
	}
	for index, src := range sources {
		srcBytes := []byte(src)
		file, diags := Parse(srcBytes, nil)
		if file.Span.Start != 0 || file.Span.End != len(srcBytes) {
			t.Fatalf("case %d: file span %v", index, file.Span)
		}
		for _, d := range diags {
			checkSpan(t, index, srcBytes, d.Span)
		}
		for _, line := range file.Doc.Lines {
			checkSpan(t, index, srcBytes, line.Stmt.Bounds())
		}
	}
}

func checkSpan(t *testing.T, index int, src []byte, span source.Span) {
	t.Helper()
	if span.Start < 0 || span.End > len(src) || span.Start > span.End {
		t.Fatalf("case %d: span %v outside a source of %d bytes", index, span, len(src))
	}
	if span.Start < len(src) && !utf8.RuneStart(src[span.Start]) {
		t.Fatalf("case %d: span start %d splits a rune", index, span.Start)
	}
	if span.End < len(src) && !utf8.RuneStart(src[span.End]) {
		t.Fatalf("case %d: span end %d splits a rune", index, span.End)
	}
}
