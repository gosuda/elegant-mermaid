package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/quadrant"
)

func quadrantRule(m *quadrant.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	switch row.Code {
	case "quadrant/duplicate-point":
		out = quadrantDuplicatePoints(m, row)
	case "quadrant/duplicate-quadrant":
		out = quadrantDuplicateDeclarations(m, row)
	default:
		if quadrantHeaderMissing(m, row) {
			out = append(out, diagnostic(row, row.Summary, m.HeaderSpan))
		}
	}
	for i := range out {
		out[i].Help = row.Help
	}
	return out
}

func quadrantHeaderMissing(m *quadrant.Model, row Row) bool {
	switch row.Code {
	case "quadrant/no-points":
		return len(m.Points) == 0 && (m.HasXAxis || m.HasYAxis || len(m.QuadrantDeclarations) > 0)
	case "quadrant/missing-x-axis":
		return len(m.Points) > 0 && !m.HasXAxis
	case "quadrant/missing-y-axis":
		return len(m.Points) > 0 && !m.HasYAxis
	default:
		return false
	}
}

func quadrantDuplicatePoints(m *quadrant.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	names := map[string]bool{}
	for _, point := range m.Points {
		if names[point.LabelKey] {
			out = append(out, diagnostic(row, row.Summary, point.LabelSpan))
		}
		names[point.LabelKey] = true
	}
	return out
}

func quadrantDuplicateDeclarations(m *quadrant.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	regions := map[int]bool{}
	for _, declaration := range m.QuadrantDeclarations {
		if regions[declaration.Number] {
			out = append(out, diagnostic(row, row.Summary, declaration.Span))
		}
		regions[declaration.Number] = true
	}
	return out
}
