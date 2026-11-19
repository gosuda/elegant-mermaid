package lint

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/block"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func blockNoBlocks(m *model.Model, row Row) []diag.Diagnostic {
	if m.Root == nil || !blockHasDeclaration(m.Root.Children) {
		return []diag.Diagnostic{diagnostic(row, row.Summary, source.Span{})}
	}
	return nil
}

func blockHasDeclaration(children []*model.Block) bool {
	for _, child := range children {
		if child.Type != "space" {
			return true
		}
	}
	return false
}
