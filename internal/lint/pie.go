package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/pie"
)

func pieRules(m *pie.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := map[string]bool{}
	for _, item := range m.Occurrences {
		label := item.Label
		if item.Section >= 0 {
			label = m.Sections[item.Section].Label
		}
		if row.Code == "pie/duplicate-label" && seen[label] {
			out = append(out, diagnostic(row, row.Summary, item.LabelSpan))
		}
		seen[label] = true
		if row.Code == "pie/zero-value" && item.ExactZero {
			out = append(out, diagnostic(row, row.Summary, item.NumberSpan))
		}
	}
	if row.Code == "pie/no-data" && len(m.Occurrences) == 0 {
		out = append(out, diagnostic(row, row.Summary, m.Header))
	}
	return out
}
