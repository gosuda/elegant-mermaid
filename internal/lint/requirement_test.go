package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/requirement"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/requirement"
)

func TestRequirementLintRules(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"requirement/duplicate-name", "requirementDiagram\nrequirement A {\nid: 1\n}\nelement A {\ntype: \"test\"\n}\n", "requirementDiagram\nrequirement A {\nid: 1\n}\nelement B {\ntype: \"test\"\n}\n"},
		{"requirement/duplicate-id", "requirementDiagram\nrequirement A {\nid: 1\n}\nrequirement A {\nid: 2\n}\nrequirement B {\nid: 2\n}\n", "requirementDiagram\nrequirement A {\nid: 1\n}\nrequirement A {\nid: 2\n}\nrequirement B {\nid: 3\n}\n"},
		{"requirement/duplicate-id", "requirementDiagram\nrequirement A {\nid: 1\n}\nrequirement B {\nid: 1\n}\n", "requirementDiagram\nrequirement A {\nid: 1\n}\nrequirement B {\nid: 2\n}\n"},
		{"requirement/undefined-reference", "requirementDiagram\nrequirement A {\nid: 1\n}\nA - satisfies -> B\n", "requirementDiagram\nA - satisfies -> B\nrequirement A {\nid: 1\n}\nelement B {\ntype: \"test\"\n}\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			row := Row{Code: tc.code, Summary: "finding", Help: "help"}
			for _, input := range []struct {
				source string
				want   int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkRequirementRuleCase(t, tc.code, input.source, input.want, row)
			}
		})
	}
}

func checkRequirementRuleCase(t *testing.T, code, text string, want int, row Row) {
	t.Helper()
	src := []byte(text)
	parsed, diagnostics := syn.Parse(src, nil)
	if len(diagnostics) != 0 {
		t.Fatalf("parse diagnostics: %+v", diagnostics)
	}
	m, diagnostics := model.Resolve(src, parsed)
	if len(diagnostics) != 0 {
		t.Fatalf("resolve diagnostics: %+v", diagnostics)
	}
	got := requirementLint(m, row)
	checkResolvedRuleDiagnostics(t, text, Row{Code: code, Summary: "finding", Help: "help"}, got, want)
	for _, d := range got {
		if d.Span.End <= d.Span.Start {
			t.Fatalf("bad diagnostic: %+v", d)
		}
	}
}
