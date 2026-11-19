package lint

import "testing"

func TestClassLintRules(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"class/duplicate-class", "classDiagram\nclass A\nclass A\n", "classDiagram\nclass A\nclass B\n"},
		{"class/no-duplicate-methods", "classDiagram\nclass A {\n+run() void\n+run() void\n}\n", "classDiagram\nclass A {\n+run() void\n+stop() void\n}\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			row := Row{Code: tc.code, Summary: "finding", Help: "help"}
			for _, input := range []struct {
				source string
				want   int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkClassRuleCase(t, tc.code, input.source, input.want, row)
			}
		})
	}
}

func checkClassRuleCase(t *testing.T, code, text string, want int, row Row) {
	t.Helper()
	a := Analyze([]byte(text))
	a.parseKind()
	got := classLint(a.classModel, row)
	if len(got) != want {
		t.Fatalf("%s: got %d findings, want %d", text, len(got), want)
	}
	for _, d := range got {
		if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.Start < 0 || d.Span.End > len(text) || d.Span.End <= d.Span.Start {
			t.Fatalf("bad diagnostic: %+v", d)
		}
	}
}
