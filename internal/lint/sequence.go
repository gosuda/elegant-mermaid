package lint

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/sequence"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func sequenceDuplicateParticipant(m *model.Model, row Row) []diag.Diagnostic {
	seen := make(map[string]bool)
	var out []diag.Diagnostic
	for _, d := range m.Declarations {
		if seen[d.ID] {
			out = append(out, diagnostic(row, row.Summary, d.Span))
		}
		seen[d.ID] = true
	}
	return out
}

func sequencePreferExplicitParticipants(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	seen := make([]bool, len(m.Actors))
	for _, event := range m.Events {
		message, ok := event.(*model.Message)
		if !ok {
			continue
		}
		for _, index := range []int{message.From, message.To} {
			if seen[index] {
				continue
			}
			seen[index] = true
			actor := m.Actors[index]
			declared := slices.ContainsFunc(m.Declarations, func(d model.ActorDeclaration) bool { return d.ID == actor.ID && d.Span.Start < message.Span.Start })
			if !declared {
				out = append(out, diagnostic(row, row.Summary, actor.Span))
			}
		}
	}
	return out
}

func sequenceNoActivateWithoutDeactivate(m *model.Model, row Row) []diag.Diagnostic {
	stacks := make([][]source.Span, len(m.Actors))
	var spans []source.Span
	for _, activation := range m.ActivationHistory {
		stack := stacks[activation.Actor]
		if activation.Open {
			stacks[activation.Actor] = append(stack, activation.Span)
			continue
		}
		if len(stack) == 0 {
			spans = append(spans, activation.Span)
			continue
		}
		stacks[activation.Actor] = stack[:len(stack)-1]
	}
	for _, stack := range stacks {
		spans = append(spans, stack...)
	}
	slices.SortFunc(spans, func(a, b source.Span) int { return a.Start - b.Start })
	var out []diag.Diagnostic
	for _, span := range spans {
		out = append(out, diagnostic(row, row.Summary, span))
	}
	return out
}
