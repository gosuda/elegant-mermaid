package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/xychart"
)

func xychartMissingXAxis(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Plots) > 0 && m.X.Span.Start == m.X.Span.End {
		return []diag.Diagnostic{diagnostic(row, row.Summary, m.HeaderSpan)}
	}
	return nil
}

func xychartMissingYAxis(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Plots) > 0 && m.Y.Span.Start == m.Y.Span.End {
		return []diag.Diagnostic{diagnostic(row, row.Summary, m.HeaderSpan)}
	}
	return nil
}

func xychartNoSeries(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Plots) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, m.HeaderSpan)}
	}
	return nil
}

func xychartSeriesLengthMismatch(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	n := -1
	if m.X.Band {
		n = len(m.X.Categories)
	}
	for _, plot := range m.Plots {
		if n < 0 {
			n = plot.RawPointCount
		}
		if plot.RawPointCount != n {
			out = append(out, diagnostic(row, row.Summary, plot.Span))
		}
	}
	return out
}
