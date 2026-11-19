package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/treeview"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func treeviewNoNodes(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Nodes) <= 1 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, source.Span{})}
	}
	return nil
}

func treeviewDuplicateSibling(m *model.Model, row Row) []diag.Diagnostic {
	type key struct {
		parent int
		name   string
	}
	seen := make(map[key]bool)
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		if n.Parent == model.NoParent {
			continue
		}
		k := key{n.Parent, n.Name}
		if seen[k] {
			out = append(out, diagnostic(row, row.Summary, n.Span))
		}
		seen[k] = true
	}
	return out
}
