package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/block"
	syntax "github.com/gosuda/elegant-mermaid/internal/syntax/block"
)

func TestBlockNoBlocks(t *testing.T) {
	row := Row{Code: "block/no-blocks", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"block-beta\n", 1},
		{"block-beta\nA[\"alpha\"]\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := blockNoBlocks(resolved, row)
		if len(got) != tc.want {
			t.Fatalf("%q: got %v, want %d diagnostics", tc.source, got, tc.want)
		}
		for _, d := range got {
			if d.Code != row.Code || d.Message != row.Summary || d.Help != row.Help || d.Span.Start < 0 || d.Span.End > len(tc.source) {
				t.Fatalf("unexpected diagnostic: %+v", d)
			}
		}
	}
}
