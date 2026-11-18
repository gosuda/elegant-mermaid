package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/mindmap"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func mindmapDuplicateSibling(m *model.Model, row Row) []diag.Diagnostic {
	type key struct {
		parent int
		label  string
	}
	seen := make(map[key]bool)
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		k := key{n.Parent, n.Label}
		if n.Parent != model.NoParent && seen[k] {
			out = append(out, diagnostic(row, row.Summary, n.Span))
		}
		seen[k] = true
	}
	return out
}

func mindmapNoNodes(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Nodes) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, source.Span{})}
	}
	return nil
}

func mindmapDeepNesting(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		depth, parent := 1, n.Parent
		for parent >= 0 && parent < len(m.Nodes) && depth <= len(m.Nodes) {
			depth++
			parent = m.Nodes[parent].Parent
		}
		if depth > 5 {
			out = append(out, diagnostic(row, row.Summary, n.Span))
		}
	}
	return out
}
