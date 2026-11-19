package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/gitgraph"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func gitgraphDuplicateTag(m *model.Model, row Row) []diag.Diagnostic {
	seen := make(map[string]int)
	var out []diag.Diagnostic
	for i, c := range m.CommitHistory {
		for _, tag := range c.Tags {
			if prior, ok := seen[tag]; ok && prior != i {
				out = append(out, diagnostic(row, row.Summary, c.Span))
			}
			seen[tag] = i
		}
	}
	return out
}

func gitgraphNoCommits(m *model.Model, row Row) []diag.Diagnostic {
	if len(m.Commits) == 0 {
		return []diag.Diagnostic{diagnostic(row, row.Summary, source.Span{})}
	}
	return nil
}
