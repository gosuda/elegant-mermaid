package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/architecture"
)

func architectureNoElements(m *architecture.Model, row Row) []diag.Diagnostic {
	if m.ElementDeclarations == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, m.HeaderSpan)}
	}
	return nil
}

func architectureNoEdges(m *architecture.Model, row Row) []diag.Diagnostic {
	if m.ElementDeclarations > 0 && len(m.EdgeDeclarations) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, m.HeaderSpan)}
	}
	return nil
}

func architectureDuplicateEdge(m *architecture.Model, row Row) []diag.Diagnostic {
	type key struct {
		from, to, fromSide, toSide           string
		fromGroup, toGroup, fromInto, toInto bool
	}
	seen := make(map[key]bool)
	var out []diag.Diagnostic
	for _, declaration := range m.EdgeDeclarations {
		e := declaration.Rejected
		if e == nil {
			e = &m.Edges[declaration.EdgeIndex]
		}
		k := key{e.From, e.To, e.FromSide, e.ToSide, e.FromGroup, e.ToGroup, e.FromInto, e.ToInto}
		if seen[k] {
			out = append(out, diagnostic(row, row.Summary, e.Span))
		}
		seen[k] = true
	}
	return out
}
