package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/kanban"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func kanbanNoColumns(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Sections) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, source.Span{})}
	}
	return nil
}
func kanbanEmptyColumn(m *model.Model, row Row) []diag.Diagnostic {
	occupied := make(map[int]bool)
	for _, n := range m.Nodes {
		occupied[n.Parent] = true
	}
	var out []diag.Diagnostic
	for _, i := range m.Sections {
		if !occupied[i] {
			out = append(out, diagnostic(row, row.Summary, m.Nodes[i].Anchor))
		}
	}
	return out
}
func kanbanDuplicateColumn(m *model.Model, row Row) []diag.Diagnostic {
	seen := make(map[string]bool)
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		if seen[n.ID] && n.IsSection() {
			out = append(out, diagnostic(row, row.Summary, n.Anchor))
		}
		seen[n.ID] = true
	}
	return out
}
func kanbanDuplicateTaskID(m *model.Model, row Row) []diag.Diagnostic {
	seen := make(map[string]bool)
	var out []diag.Diagnostic
	for _, n := range m.Nodes {
		if seen[n.ID] && !n.IsSection() {
			out = append(out, diagnostic(row, row.Summary, n.Anchor))
		}
		seen[n.ID] = true
	}
	return out
}
