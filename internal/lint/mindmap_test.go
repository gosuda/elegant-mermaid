package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/mindmap"
	syntax "github.com/gosuda/elegant-mermaid/internal/syntax/mindmap"
)

func TestMindmapDuplicateSibling(t *testing.T) {
	row := Row{Code: "mindmap/duplicate-sibling", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"mindmap\n  root\n    same\n    same\n", 1},
		{"mindmap\n  root\n    same\n    other\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := mindmapDuplicateSibling(resolved, row)
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

func TestMindmapNoNodes(t *testing.T) {
	row := Row{Code: "mindmap/no-nodes", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"mindmap\n", 1},
		{"mindmap\n  root\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := mindmapNoNodes(resolved, row)
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

func TestMindmapDeepNesting(t *testing.T) {
	row := Row{Code: "mindmap/deep-nesting", Summary: "rule message", Help: "rule help"}
	for _, tc := range []struct {
		source string
		want   int
	}{
		{"mindmap\n  root\n    a\n      b\n        c\n          d\n            e\n              f\n", 2},
		{"mindmap\n  root\n    a\n", 0},
	} {
		parsed, _ := syntax.Parse([]byte(tc.source), nil)
		resolved, _ := model.Resolve([]byte(tc.source), parsed)
		got := mindmapDeepNesting(resolved, row)
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
