package lint

import "testing"

func TestC4LintRules(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"c4/duplicate-id", "C4Context\nPerson(a, \"A\")\nSystem(a, \"B\")\n", "C4Context\nPerson(a, \"A\")\nSystem(b, \"B\")\n"},
		{"c4/undefined-relationship-endpoint", "C4Context\nPerson(a, \"A\")\nRel(a, b, \"uses\")\n", "C4Context\nRel(a, b, \"uses\")\nPerson(a, \"A\")\nSystem(b, \"B\")\n"},
		{"c4/undefined-element-style", "C4Context\nUpdateElementStyle(a, $bgColor=\"red\")\n", "C4Context\nUpdateElementStyle(a, $bgColor=\"red\")\nPerson(a, \"A\")\n"},
		{"c4/undefined-relationship-style-endpoint", "C4Context\nPerson(a, \"A\")\nUpdateRelStyle(a, b, $textColor=\"red\")\n", "C4Context\nUpdateRelStyle(a, b, $textColor=\"red\")\nPerson(a, \"A\")\nSystem(b, \"B\")\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			row := Row{Code: tc.code, Summary: "finding", Help: "help"}
			for _, input := range []struct {
				source string
				want   int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkC4RuleCase(t, tc.code, input.source, input.want, row)
			}
		})
	}
}

func checkC4RuleCase(t *testing.T, code, text string, want int, row Row) {
	t.Helper()
	a := Analyze([]byte(text))
	a.parseKind()
	got := c4Lint(a.c4Model, row)
	if len(got) != want {
		t.Fatalf("%s: got %d findings, want %d", text, len(got), want)
	}
	for _, d := range got {
		if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.Start < 0 || d.Span.End > len(text) || d.Span.End <= d.Span.Start {
			t.Fatalf("bad diagnostic: %+v", d)
		}
	}
}
