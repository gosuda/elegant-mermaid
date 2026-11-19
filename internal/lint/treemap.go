package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/treemap"
)

func treemapLint(m *treemap.Model, row Row) []diag.Diagnostic {
	if row.Code == "treemap/duplicate-sibling" {
		return treemapDuplicateSiblings(m, row)
	}
	var out []diag.Diagnostic
	leaves := 0
	for _, node := range m.Nodes {
		if !node.Leaf {
			continue
		}
		leaves++
		if row.Code == "treemap/zero-value" && node.ExactZero {
			out = append(out, diagnostic(row, row.Summary, node.ValueSpan))
		}
		if row.Code == "treemap/branch-with-value" && node.NextMoreIndented {
			out = append(out, diagnostic(row, row.Summary, node.NameSpan))
		}
	}
	if row.Code == "treemap/no-leaves" && leaves == 0 {
		out = append(out, diagnostic(row, row.Summary, m.Span))
	}
	return out
}

func treemapDuplicateSiblings(m *treemap.Model, row Row) []diag.Diagnostic {
	type sibling struct {
		parent int
		name   string
	}
	var out []diag.Diagnostic
	seen := make(map[sibling]bool)
	for _, node := range m.Nodes {
		key := sibling{node.ParentIndex, node.Name}
		if seen[key] {
			out = append(out, diagnostic(row, row.Summary, node.NameSpan))
		}
		seen[key] = true
	}
	return out
}
