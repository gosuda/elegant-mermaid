package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/radar"
)

func radarNoCurves(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Curves) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, m.HeaderSpan)}
	}
	return nil
}

func radarCurveLengthMismatch(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, c := range m.Curves {
		if c.Positional && c.EntryCount != len(m.Axes) {
			out = append(out, diagnostic(row, row.Summary, c.Span))
		}
	}
	return out
}

func radarDuplicateAxis(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := make(map[string]bool)
	for _, a := range m.Axes {
		if seen[a.Label] {
			out = append(out, diagnostic(row, row.Summary, a.Span))
		}
		seen[a.Label] = true
	}
	return out
}
