package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/ishikawa"
)

func ishikawaNoCauses(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Nodes) == 1 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, m.Nodes[0].Span)}
	}
	return nil
}
func ishikawaEmptyCategory(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		if n.Depth == 1 && len(n.Children) == 0 {
			out = append(out, diagnostic(row, row.Summary, n.Span))
		}
	}
	return out
}
func ishikawaDeepNesting(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		if n.Depth >= 5 {
			out = append(out, diagnostic(row, row.Summary, n.Span))
		}
	}
	return out
}
func ishikawaDuplicateSibling(m *model.Model, row Row) []diag.Diagnostic {
	type key struct {
		parent int
		label  string
	}
	seen := make(map[key]bool)
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		if n.Parent == model.NoParent {
			continue
		}
		k := key{n.Parent, n.Label}
		if seen[k] {
			out = append(out, diagnostic(row, row.Summary, n.Span))
		}
		seen[k] = true
	}
	return out
}
