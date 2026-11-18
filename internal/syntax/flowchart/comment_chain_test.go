package flowchart_test

import (
	"slices"
	"testing"

	flowmodel "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	flowparser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func TestCommentLineKeepsChainOpen(t *testing.T) {
	edges := func(src string) ([][2]string, int) {
		t.Helper()
		text := []byte(src)
		pre := syntax.Preprocess(text)
		ast, parsed := flowparser.Parse(text, pre.Removed)
		model, resolved := flowmodel.Resolve(text, ast)
		var got [][2]string
		for _, e := range model.Edges {
			got = append(got, [2]string{e.From, e.To})
		}
		return got, len(pre.Diags) + len(parsed) + len(resolved)
	}
	blank, blankDiags := edges("flowchart TD\nA --> B\n  --> C\n\n  --> H\n")
	comment, commentDiags := edges("flowchart TD\nA --> B\n  --> C\n  %% c\n  --> H\n")
	if blankDiags != 0 || commentDiags != 0 {
		t.Fatalf("diagnostics: blank line %d, comment line %d, want 0", blankDiags, commentDiags)
	}
	want := [][2]string{{"A", "B"}, {"B", "C"}, {"C", "H"}}
	if !slices.Equal(blank, want) || !slices.Equal(comment, want) {
		t.Fatalf("edges: blank line %v, comment line %v, want %v", blank, comment, want)
	}
}
