package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/state"
)

func stateLint(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	var walk func([]model.StatementOccurrence)
	walk = func(statements []model.StatementOccurrence) {
		ids := map[string]bool{}
		transitions := map[[3]string]bool{}
		for _, s := range statements {
			if s.HasBody && s.StatementCount == 0 && row.Code == "state/empty-composite" {
				out = append(out, diagnostic(row, row.Summary, s.Span))
			}
			walk(s.Body)
			if stateOccurrenceMatches(s, row.Code, ids, transitions) {
				out = append(out, diagnostic(row, row.Summary, s.Span))
			}
		}
	}
	walk(m.Occurrences)
	return out
}

func stateOccurrenceMatches(s model.StatementOccurrence, code string, ids map[string]bool, transitions map[[3]string]bool) bool {
	if s.ID != "" {
		duplicate := ids[s.ID]
		ids[s.ID] = true
		return code == "state/duplicate-state" && duplicate
	}
	if s.From == "" {
		return false
	}
	key := [3]string{s.From, s.To, s.Label}
	duplicate := transitions[key]
	transitions[key] = true
	return code == "state/duplicate-transition" && duplicate ||
		code == "state/self-transition" && s.From == s.To && s.From != "[*]"
}
