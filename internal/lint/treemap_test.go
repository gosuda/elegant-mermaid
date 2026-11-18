package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/treemap"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/treemap"
)

func TestTreemapLintPredicates(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"treemap/zero-value", "treemap\n\"A\": 0\n", "treemap\n\"A\": 1\n"},
		{"treemap/no-leaves", "treemap\n\"Group\"\n", "treemap\n\"A\": 1\n"},
		{"treemap/duplicate-sibling", "treemap\n\"A\": 1\n\"A\": 2\n", "treemap\n\"P\"\n  \"A\": 1\n\"Q\"\n  \"A\": 2\n"},
		{"treemap/branch-with-value", "treemap\n\"A\": 1\n  \"B\": 2\n", "treemap\n\"A\": 1\n\"B\": 2\n"},
		{"treemap/duplicate-sibling", "treemap\n\"B\"\n\"A\": 1\n  \"B\"\n", "treemap\n\"B\"\n\"A\"\n  \"B\"\n"},
		{"treemap/zero-value", "treemap\n\"A\": 0.\n", "treemap\n\"A\": 0.0001\n"},
		{"treemap/zero-value", "treemap\n\"A\": 0_0\n", "treemap\n\"A\": 0.0001\n"},
		{"treemap/zero-value", "treemap\n\"A\": 0,0\n", "treemap\n\"A\": 0.0001\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			for _, input := range []struct {
				text string
				want int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkTreemapRuleCase(t, tc.code, input.text, input.want)
			}
		})
	}
}

func checkTreemapRuleCase(t *testing.T, code, text string, want int) {
	t.Helper()
	file, errors := syn.Parse([]byte(text), nil)
	if len(errors) != 0 {
		t.Fatalf("parse: %+v", errors)
	}
	model, errors := treemap.Resolve([]byte(text), file)
	if len(errors) != 0 {
		t.Fatalf("resolve: %+v", errors)
	}
	got := treemapLint(model, Row{Code: code, Summary: "finding", Help: "help"})
	if len(got) != want {
		t.Fatalf("%s: %+v", text, got)
	}
	for _, d := range got {
		checkTreemapFinding1(t, d, code, text)
	}
}

func checkTreemapFinding1(t *testing.T, d diag.Diagnostic, code string, text string) {
	t.Helper()
	if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.Start < 0 || d.Span.End > len(text) || d.Span.End <= d.Span.Start {
		t.Fatalf("bad finding: %+v", d)
	}
}

func TestTreemapValuedLeafEvidenceSpans(t *testing.T) {
	text := "treemap\n\"B\"\n\"A\": 1\n  \"B\"\n"
	file, errors := syn.Parse([]byte(text), nil)
	if len(errors) != 0 {
		t.Fatalf("parse: %+v", errors)
	}
	model, errors := treemap.Resolve([]byte(text), file)
	if len(errors) != 0 {
		t.Fatalf("resolve: %+v", errors)
	}
	for code, start := range map[string]int{"treemap/duplicate-sibling": 21, "treemap/branch-with-value": 12} {
		got := treemapLint(model, Row{Code: code})
		if len(got) != 1 || got[0].Span.Start != start {
			t.Fatalf("%s: %+v", code, got)
		}
	}
}
