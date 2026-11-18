package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/model/pie"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/pie"
)

func TestPieRulePredicates(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"pie/duplicate-label", "pie\n\"A\": 1\n\"A\": 2\n", "pie\n\"A\": 1\n\"B\": 2\n"},
		{"pie/zero-value", "pie\n\"A\": 0\n", "pie\n\"A\": 0.0001\n"},
		{"pie/no-data", "pie\n", "pie\n\"A\": 1\n"},
		{"pie/duplicate-label", "pie\n\"A\":0.0001\n\"A\":0\n", "pie\n\"A\":-1\n"},
		{"pie/zero-value", "pie\n\"A\":0.0001\n\"A\":0\n", "pie\n\"A\":-1\n"},
		{"pie/no-data", "pie\n", "pie\n\"A\":-1\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			for _, input := range []struct {
				text string
				want int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkPieRuleCase(t, tc.code, input.text, input.want)
			}
		})
	}
}

func checkPieRuleCase(t *testing.T, code, text string, want int) {
	t.Helper()
	document, diagnostics := syn.Parse([]byte(text), nil)
	if len(diagnostics) != 0 {
		t.Fatalf("parse: %+v", diagnostics)
	}
	model, modelDiagnostics := pie.Resolve([]byte(text), document)
	for _, d := range modelDiagnostics {
		if d.Code != "pie/negative-value" {
			t.Fatalf("resolve: %+v", modelDiagnostics)
		}
	}
	row := Row{Code: code, Summary: "finding", Help: "help"}
	got := pieRules(model, row)
	if len(got) != want {
		t.Fatalf("%s: got %+v", text, got)
	}
	for _, d := range got {
		if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.End > len(text) {
			t.Fatalf("bad finding: %+v", d)
		}
	}
}
