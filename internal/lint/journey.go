package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/journey"
)

func journeyRules(m *journey.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	switch row.Code {
	case "journey/empty-section":
		return journeyEmptySections(m, row)
	case "journey/task-without-actor":
		for _, task := range m.Tasks {
			if task.WithoutActor {
				out = append(out, diagnostic(row, row.Summary, task.NameSpan))
			}
		}
	case "journey/no-tasks":
		if len(m.Tasks) == 0 {
			out = append(out, diagnostic(row, row.Summary, m.HeaderSpan))
		}
	}
	return out
}

func journeyEmptySections(m *journey.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	task := 0
	for _, section := range m.Sections {
		for task < len(m.Tasks) && m.Tasks[task].SectionSpan.Start < section.Span.Start {
			task++
		}
		if task == len(m.Tasks) || m.Tasks[task].SectionSpan != section.Span {
			out = append(out, diagnostic(row, row.Summary, section.Span))
		}
	}
	return out
}
