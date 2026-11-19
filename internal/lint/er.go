package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/er"
)

func ERDuplicateAttribute(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, declaration := range m.Declarations {
		names := map[string]bool{}
		for _, attr := range m.Entities[declaration.Entity].Attributes[declaration.AttributeStart:declaration.AttributeEnd] {
			if names[attr.Name] {
				out = append(out, diagnostic(row, row.Summary, attr.NameSpan))
			}
			names[attr.Name] = true
		}
	}
	return out
}

func ERDuplicateEntity(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := make([]bool, len(m.Entities))
	for _, declaration := range m.Declarations {
		if seen[declaration.Entity] {
			out = append(out, diagnostic(row, row.Summary, declaration.NameSpan))
		}
		seen[declaration.Entity] = true
	}
	return out
}

func ERStandaloneEntity(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	related := map[string]bool{}
	for _, relationship := range m.Relationships {
		related[relationship.From] = true
		related[relationship.To] = true
	}
	for _, declaration := range m.Declarations {
		if !related[m.Entities[declaration.Entity].ID] {
			out = append(out, diagnostic(row, row.Summary, declaration.NameSpan))
		}
	}
	return out
}
