package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/journey"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/journey"
)

func TestJourneyRulePredicates(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"journey/empty-section", "journey\nsection A\nsection A\nTask: 3: Bob\n", "journey\nsection A\nTask: 3: Bob\nsection A\nTask: 3: Bob\n"},
		{"journey/task-without-actor", "journey\nTask: 3\n", "journey\nTask: 3: Bob\n"},
		{"journey/no-tasks", "journey\n", "journey\nTask: 3: Bob\n"},
		{"journey/task-without-actor", "journey\nTask: 3: , ,\n", "journey\nTask: 3: \u00a0\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			for _, input := range []struct {
				text string
				want int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkJourneyRuleCase(t, tc.code, input.text, input.want)
			}
		})
	}
}

func checkJourneyRuleCase(t *testing.T, code, text string, want int) {
	t.Helper()
	document, parseDiags := syn.Parse([]byte(text), nil)
	if len(parseDiags) != 0 {
		t.Fatalf("parse: %+v", parseDiags)
	}
	model, resolveDiags := journey.Resolve([]byte(text), document)
	if len(resolveDiags) != 0 {
		t.Fatalf("resolve: %+v", resolveDiags)
	}
	row := Row{Code: code, Summary: "finding", Help: "help"}
	got := journeyRules(model, row)
	if len(got) != want {
		t.Fatalf("%s: got %+v", text, got)
	}
	for _, d := range got {
		checkJourneyFinding(t, d, code, text)
	}
}

func checkJourneyFinding(t *testing.T, d diag.Diagnostic, code, text string) {
	t.Helper()
	if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.End > len(text) {
		t.Fatalf("bad finding: %+v", d)
	}
	wantText := "journey"
	switch code {
	case "journey/empty-section":
		wantText = "A"
	case "journey/task-without-actor":
		wantText = "Task"
	}
	if text[d.Span.Start:d.Span.End] != wantText {
		t.Fatalf("wrong finding span: %+v", d)
	}
}
