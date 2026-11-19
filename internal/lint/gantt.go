package lint

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/gantt"
)

func ganttRule(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	switch row.Code {
	case "gantt/duplicate-task-id":
		out = ganttDuplicateTasks(m, row)
	case "gantt/undefined-dependency":
		ids := map[string]bool{}
		for _, task := range m.Tasks {
			ids[task.ID] = true
		}
		for _, task := range m.Tasks {
			out = appendGanttDependencies(out, task.Start, ids, row)
			out = appendGanttDependencies(out, task.End, ids, row)
		}
	case "gantt/empty-section":
		out = ganttEmptySections(m, row)
	}
	for i := range out {
		out[i].Help = row.Help
	}
	return out
}

func ganttDuplicateTasks(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := map[string]bool{}
	for _, task := range m.Tasks {
		if task.Generated {
			continue
		}
		if seen[task.ID] {
			out = append(out, diagnostic(row, row.Summary, task.DataSpan))
		}
		seen[task.ID] = true
	}
	return out
}

func ganttEmptySections(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	occupied := make([]bool, len(m.Sections))
	for _, task := range m.Tasks {
		if task.Section >= 0 && task.Section < len(occupied) {
			occupied[task.Section] = true
		}
	}
	for i, section := range m.Sections {
		if !occupied[i] {
			out = append(out, diagnostic(row, row.Summary, section.Span))
		}
	}
	return out
}

func appendGanttDependencies(out []diag.Diagnostic, operand model.Operand, ids map[string]bool, row Row) []diag.Diagnostic {
	words := strings.Fields(operand.Text)
	if len(words) <= 1 || (words[0] != "after" && words[0] != "until") {
		return out
	}
	for _, id := range words[1:] {
		if !ids[id] {
			out = append(out, diagnostic(row, row.Summary, operand.Span))
		}
	}
	return out
}
