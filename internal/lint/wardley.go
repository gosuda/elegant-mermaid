package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/wardley"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func wardleyRule(m *wardley.Model, row Row) []diag.Diagnostic {
	names := map[string]bool{}
	used := map[string]bool{}
	for _, d := range m.Declarations {
		names[m.Nodes[d.Node].ID] = true
	}
	for _, r := range m.References {
		used[m.ReferenceName(r)] = true
	}
	for _, r := range m.PipelineUses {
		used[m.ReferenceName(r)] = true
	}
	out, scale := wardleyDeclarationFindings(m, row, used)
	emit := func(span source.Span) { out = append(out, diagnostic(row, row.Summary, span)) }
	if row.Code == "wardley/undefined-component" {
		out = wardleyUndefinedComponents(m, row, names, out)
	}
	if row.Code == "wardley/no-components" && len(names) == 0 ||
		row.Code == "wardley/mixed-coordinate-scale" && scale == 3 {
		emit(m.Header)
	}
	for i := range out {
		out[i].Help = row.Help
	}
	return out
}

func wardleyDeclarationFindings(m *wardley.Model, row Row, used map[string]bool) ([]diag.Diagnostic, uint8) {
	var out []diag.Diagnostic
	seen := map[string]bool{}
	var scale uint8
	for _, d := range m.Declarations {
		name := m.Nodes[d.Node].ID
		if seen[name] && row.Code == "wardley/duplicate-component" ||
			!used[name] && row.Code == "wardley/orphan-component" {
			out = append(out, diagnostic(row, row.Summary, d.Span))
		}
		seen[name] = true
		scale |= d.Scale
	}
	return out, scale
}

func wardleyUndefinedComponents(m *wardley.Model, row Row, names map[string]bool, out []diag.Diagnostic) []diag.Diagnostic {
	for _, r := range m.References {
		if !names[m.ReferenceName(r)] {
			out = append(out, diagnostic(row, row.Summary, r.Span))
		}
	}
	return out
}
