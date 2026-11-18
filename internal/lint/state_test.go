package lint

import (
	"testing"

	model "github.com/gosuda/elegant-mermaid/internal/model/state"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/state"
)

func TestStateLintRules(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"state/duplicate-state", "stateDiagram-v2\nstate A\nstate A\n", "stateDiagram-v2\nstate A\nstate B\n"},
		{"state/duplicate-transition", "stateDiagram-v2\nA --> B: go\nA --> B: go\n", "stateDiagram-v2\nA --> B: go\nA --> B: stop\n"},
		{"state/empty-composite", "stateDiagram-v2\nstate A {\n}\n", "stateDiagram-v2\nstate A {\nstate B\n}\n"},
		{"state/self-transition", "stateDiagram-v2\nA --> A: go\n", "stateDiagram-v2\nA --> B: go\n"},
		{"state/empty-composite", "stateDiagram-v2\nstate A {\n}\n", "stateDiagram-v2\nstate A {\ndirection LR\n}\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			row := Row{Code: tc.code, Summary: "finding", Help: "help"}
			for _, input := range []struct {
				source string
				want   int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkStateRuleCase(t, tc.code, input.source, input.want, row)
			}
		})
	}
}

func checkStateRuleCase(t *testing.T, code, text string, want int, row Row) {
	t.Helper()
	file, diagnostics := syn.Parse([]byte(text), nil)
	if len(diagnostics) != 0 {
		t.Fatalf("parse %q: %+v", text, diagnostics)
	}
	m, _ := model.Resolve([]byte(text), file)
	got := stateLint(m, row)
	if len(got) != want {
		t.Fatalf("%s: got %d findings, want %d", text, len(got), want)
	}
	for _, d := range got {
		if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.Start < 0 || d.Span.End > len(text) || d.Span.End <= d.Span.Start {
			t.Fatalf("bad diagnostic: %+v", d)
		}
	}
}

func TestStateDiscardedCompositeBody(t *testing.T) {
	row := Row{Code: "state/duplicate-state", Summary: "finding", Help: "help"}
	checkStateRuleCase(t, row.Code, "stateDiagram-v2\nstate A {\n}\nstate A {\nstate B\nstate B\n}\n", 2, row)
	checkStateRuleCase(t, row.Code, "stateDiagram-v2\nstate A <<choice>>\nstate A <<choice>>\n", 0, row)
	transition := Row{Code: "state/duplicate-transition", Summary: "finding", Help: "help"}
	checkStateRuleCase(t, transition.Code, "stateDiagram-v2\nA --> B: go\nA --> B::go\n", 0, transition)
}
