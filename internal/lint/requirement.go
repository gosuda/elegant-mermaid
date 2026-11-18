package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/requirement"
)

func requirementLint(m *model.Model, row Row) []diag.Diagnostic {
	switch row.Code {
	case "requirement/duplicate-name":
		return requirementDuplicateNames(m, row)
	case "requirement/duplicate-id":
		return requirementDuplicateIDs(m, row)
	case "requirement/undefined-reference":
		return requirementUndefinedRefs(m, row)
	}
	return nil
}

func requirementDuplicateNames(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := map[string]bool{}
	for _, declaration := range m.Declarations {
		name := ""
		if declaration.Node.Element {
			name = m.Elements[declaration.Node.Index].Name
		} else {
			name = m.Requirements[declaration.Node.Index].Name
		}
		if name == "" {
			continue
		}
		if seen[name] {
			out = append(out, diagnostic(row, row.Summary, declaration.Span))
		}
		seen[name] = true
	}
	return out
}

func requirementDuplicateIDs(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := map[string]bool{}
	for _, declaration := range m.IDDeclarations {
		value := declaration.Discarded
		if declaration.Requirement >= 0 {
			value = m.Requirements[declaration.Requirement].Fields[declaration.Field].Value
		}
		if seen[value.Value] {
			out = append(out, diagnostic(row, row.Summary, value.Span))
		}
		seen[value.Value] = true
	}
	return out
}

func requirementUndefinedRefs(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, relation := range m.Relationships {
		first, second := relation.From, relation.To
		firstNode, secondNode := relation.FromNode, relation.ToNode
		if first.Span.Start > second.Span.Start {
			first, second = second, first
			firstNode, secondNode = secondNode, firstNode
		}
		if firstNode == nil {
			out = append(out, diagnostic(row, row.Summary, first.Span))
		}
		if secondNode == nil {
			out = append(out, diagnostic(row, row.Summary, second.Span))
		}
	}
	return out
}
