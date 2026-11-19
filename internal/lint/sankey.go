package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/sankey"
)

func sankeyLint(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := make(map[[2]int]bool)
	for _, link := range m.Links {
		key := [2]int{link.Source, link.Target}
		match := row.Code == "sankey/non-positive-value" && link.Value.Kind == model.ValueFinite && link.Value.Thousandths <= 0 ||
			row.Code == "sankey/duplicate-link" && seen[key] ||
			row.Code == "sankey/self-loop" && link.Source == link.Target
		if match {
			out = append(out, diagnostic(row, row.Summary, link.Span))
		}
		seen[key] = true
	}
	return out
}
