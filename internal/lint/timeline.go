package lint

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/timeline"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func timelineNoEntries(m *model.Model, header source.Span, row Row) []diag.Diagnostic {
	if len(m.Sections) == 0 && len(m.Periods) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, header)}
	}
	return nil
}

func timelineEmptySection(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for i, s := range m.Sections {
		found := false
		for _, p := range m.Periods {
			if p.Section == i {
				found = true
				break
			}
		}
		if !found {
			out = append(out, diagnostic(row, row.Summary, s.Span))
		}
	}
	return out
}

func timelineEmptyEvent(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, p := range m.Periods {
		for _, e := range p.Events {
			if strings.TrimSpace(e.Text) == "" {
				out = append(out, diagnostic(row, row.Summary, e.Span))
			}
		}
	}
	return out
}
