package flowchart

import (
	"strings"
	"testing"

	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func TestResolveStyleTargets(t *testing.T) {
	for _, tc := range []struct {
		name       string
		source     string
		styles     [][]string
		targets    []string
		statements []string
	}{
		{
			name:       "existing nodes",
			source:     "flowchart TD\nA --> B\nstyle A,B fill:red\n",
			styles:     [][]string{{"fill:red"}, {"fill:red"}},
			targets:    []string{"A", "B"},
			statements: []string{"style A,B fill:red", "style A,B fill:red"},
		},
		{
			name:       "implicit nodes in target order",
			source:     "flowchart TD\nstyle B,A fill:red\n",
			styles:     [][]string{{"fill:red"}, {"fill:red"}},
			targets:    []string{"B", "A"},
			statements: []string{"style B,A fill:red", "style B,A fill:red"},
		},
		{
			name:       "repeated styles append",
			source:     "flowchart TD\nA --> B\nstyle A,B fill:red\nstyle A stroke:blue\n",
			styles:     [][]string{{"fill:red", "stroke:blue"}, {"fill:red"}},
			targets:    []string{"A", "B", "A"},
			statements: []string{"style A,B fill:red", "style A,B fill:red", "style A stroke:blue"},
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			model := resolveStyleSource(t, tc.source)
			checkStyledNodes(t, []byte(tc.source), model.Nodes, tc.targets[:2], tc.styles)
			checkStyleTargets(t, tc.source, model.StyleTargets, tc.targets, tc.statements)
		})
	}
}

func resolveStyleSource(t *testing.T, text string) *Model {
	t.Helper()
	src := []byte(text)
	file, diagnostics := syn.Parse(src, nil)
	if len(diagnostics) != 0 {
		t.Fatalf("syntax diagnostics: %+v", diagnostics)
	}
	model, diagnostics := Resolve(src, file)
	if len(diagnostics) != 0 {
		t.Fatalf("model diagnostics: %+v", diagnostics)
	}
	return model
}

func checkStyledNodes(t *testing.T, src []byte, nodes []Node, ids []string, styles [][]string) {
	t.Helper()
	if len(nodes) != len(ids) {
		t.Fatalf("nodes: %+v", nodes)
	}
	for i, node := range nodes {
		if node.ID != ids[i] {
			t.Fatalf("node %d ID = %q, want %q", i, node.ID, ids[i])
		}
		checkStyleDeclarations(t, src, node.Styles.Styles, styles[i])
	}
}

func checkStyleDeclarations(t *testing.T, src []byte, styles []Style, want []string) {
	t.Helper()
	if len(styles) != len(want) {
		t.Fatalf("styles: %+v, want %+v", styles, want)
	}
	for i, style := range styles {
		if style.Text != want[i] || string(src[style.Span.Start:style.Span.End]) != style.Text {
			t.Fatalf("style %d: %+v, want %q with matching source span", i, style, want[i])
		}
	}
}

func checkStyleTargets(t *testing.T, src string, targets []StyleTarget, ids, statements []string) {
	t.Helper()
	if len(targets) != len(ids) {
		t.Fatalf("style targets: %+v", targets)
	}
	for i, target := range targets {
		if target.ID != ids[i] {
			t.Fatalf("target %d ID = %q, want %q", i, target.ID, ids[i])
		}
		statement := statements[i]
		start := strings.Index(src, statement)
		if target.Span.Start != start || target.Span.End != start+len(statement) {
			t.Fatalf("target %d span: %+v", i, target.Span)
		}
		checkStyleDeclarations(t, []byte(src), target.Styles.Styles, []string{strings.Fields(statement)[2]})
	}
}
