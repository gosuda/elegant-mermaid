package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	c4model "github.com/gosuda/elegant-mermaid/internal/model/c4"
)

func c4Lint(m *c4model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	names := make(map[string]bool, len(m.Elements)+len(m.Boundaries))
	for _, occurrence := range m.Aliases {
		d := occurrence.Declaration
		var id string
		if d.Target == c4model.DeclarationElement {
			id = m.Elements[d.Index].ID
		} else {
			id = m.Boundaries[d.Index].ID
		}
		if names[id] && row.Code == "c4/duplicate-id" {
			out = append(out, diagnostic(row, row.Summary, occurrence.Span))
		}
		names[id] = true
	}
	for _, usage := range m.Usages {
		from, to, count := c4UsageEndpoints(m, usage, row.Code)
		if count > 0 && !names[from.Value] {
			out = append(out, diagnostic(row, row.Summary, from.Span))
		}
		if count > 1 && !names[to.Value] {
			out = append(out, diagnostic(row, row.Summary, to.Span))
		}
	}
	return out
}

func c4UsageEndpoints(m *c4model.Model, usage c4model.Usage, code string) (c4model.Text, c4model.Text, int) {
	from, to := usage.From, usage.To
	switch usage.Kind {
	case c4model.UsageRelation:
		if code == "c4/undefined-relationship-endpoint" {
			from.Value = m.Relations[usage.Relation].From.Value
			to.Value = m.Relations[usage.Relation].To.Value
			return from, to, 2
		}
	case c4model.UsageElementStyle:
		if code == "c4/undefined-element-style" {
			return from, to, 1
		}
	case c4model.UsageRelationStyle:
		if code == "c4/undefined-relationship-style-endpoint" {
			return from, to, 2
		}
	}
	return from, to, 0
}
