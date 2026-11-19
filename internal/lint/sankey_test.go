package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/sankey"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/sankey"
)

func TestSankeyLintPredicates(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"sankey/non-positive-value", "A,B,0\n", "A,B,1\n"},
		{"sankey/duplicate-link", "A,B,1\nA,B,2\n", "A,B,1\nB,A,2\n"},
		{"sankey/self-loop", "A,A,1\n", "A,B,1\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			for _, input := range []struct {
				body string
				want int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkSankeyRuleCase(t, tc.code, input.body, input.want)
			}
		})
	}
}

func checkSankeyRuleCase(t *testing.T, code, text string, want int) {
	t.Helper()
	source := []byte("sankey-beta\n" + text)
	file, errors := syn.Parse(source, nil)
	if len(errors) != 0 {
		t.Fatalf("parse: %+v", errors)
	}
	m, _ := model.Resolve(source, file)
	got := sankeyLint(m, Row{Code: code, Summary: "finding", Help: "help"})
	if len(got) != want {
		t.Fatalf("%s: %+v", source, got)
	}
	for _, d := range got {
		checkSankeyFinding1(t, d, code, text)
	}
}

func checkSankeyFinding1(t *testing.T, d diag.Diagnostic, code string, text string) {
	t.Helper()
	if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.End > len("sankey-beta\n")+len(text) || d.Span.End <= d.Span.Start {
		t.Fatalf("bad finding: %+v", d)
	}
}
