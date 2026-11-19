package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/class"
)

func classLint(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	switch row.Code {
	case "class/duplicate-class":
		seen := make([]bool, len(m.Classes))
		for _, declaration := range m.Declarations {
			if seen[declaration.Class] {
				out = append(out, diagnostic(row, row.Summary, declaration.Span))
			}
			seen[declaration.Class] = true
		}
	case "class/no-duplicate-methods":
		seen := make([]map[string]bool, len(m.Classes))
		for _, member := range m.MethodCandidates {
			if seen[member.Class] == nil {
				seen[member.Class] = make(map[string]bool)
			}
			if seen[member.Class][member.Key] {
				out = append(out, diagnostic(row, row.Summary, member.Span))
			}
			seen[member.Class][member.Key] = true
		}
	}
	return out
}
