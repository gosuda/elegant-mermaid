package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/gitgraph"
	syntax "github.com/gosuda/elegant-mermaid/internal/syntax/gitgraph"
)

func TestGitgraphDuplicateTag(t *testing.T) {
	row := Row{Code: "gitgraph/duplicate-tag", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"gitGraph\ncommit tag: \"v1\"\ncommit tag: \"v1\"\n", 1},
		{"gitGraph\ncommit tag: \"v1\"\ncommit tag: \"v2\"\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := gitgraphDuplicateTag(resolved, row)
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

func TestGitgraphNoCommits(t *testing.T) {
	row := Row{Code: "gitgraph/no-commits", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"gitGraph\n", 1},
		{"gitGraph\ncommit\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := gitgraphNoCommits(resolved, row)
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
