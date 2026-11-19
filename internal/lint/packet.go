package lint

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/packet"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func packetNoFields(m *model.Model, header source.Span, row Row) []diag.Diagnostic {
	if len(m.Fields) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, header)}
	}
	return nil
}

func packetEmptyLabels(m *model.Model, row Row) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, f := range m.Fields {
		if strings.TrimSpace(f.Label) == "" {
			out = append(out, diagnostic(row, row.Summary, f.LabelSpan))
		}
	}
	return out
}
