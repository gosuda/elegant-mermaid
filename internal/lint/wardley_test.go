package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/model/wardley"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/wardley"
)

func TestWardleyRules(t *testing.T) {
	cases := []struct{ code, bad, good string }{
		{"wardley/undefined-component", "wardley-beta\ncomponent A [0.2, 0.3]\nA -> Missing\n", "wardley-beta\ncomponent A [0.2, 0.3]\ncomponent B [0.4, 0.5]\nA -> B\n"},
		{"wardley/orphan-component", "wardley-beta\ncomponent A [0.2, 0.3]\n", "wardley-beta\ncomponent A [0.2, 0.3]\nevolve A 0.5\n"},
		{"wardley/no-components", "wardley-beta\ntitle Empty\n", "wardley-beta\ncomponent A [0.2, 0.3]\n"},
		{"wardley/mixed-coordinate-scale", "wardley-beta\ncomponent A [0.2, 30.0]\n", "wardley-beta\ncomponent A [20.0, 30.0]\n"},
		{"wardley/duplicate-component", "wardley-beta\ncomponent A [0.2, 0.3]\ncomponent A [0.4, 0.5]\n", "wardley-beta\ncomponent A [0.2, 0.3]\ncomponent B [0.4, 0.5]\n"},
		{"wardley/mixed-coordinate-scale", "wardley-beta\ncomponent A [0.2, 30.0]\ncomponent A [20.0, 30.0]\n", "wardley-beta\ncomponent A [0.0, 30.0]\n"},
		{"wardley/undefined-component", "wardley-beta\nevolve Missing 0.5\n", "wardley-beta\ncomponent A [0.2, 0.3]\nevolve A 0.5\n"},
	}
	for _, c := range cases {
		t.Run(c.code, func(t *testing.T) {
			for i, text := range []string{c.bad, c.good} {
				checkWardleyRuleCase(t, c.code, text, i)
			}
		})
	}
}

func checkWardleyRuleCase(t *testing.T, code, text string, i int) {
	t.Helper()
	src := []byte(text)
	ast, parsed := syn.Parse(src, syntax.Preprocess(src).Removed)
	if len(parsed) != 0 {
		t.Fatalf("parse: %v", parsed)
	}
	m, _ := wardley.Resolve(src, ast)
	ds := wardleyRule(m, Row{Code: code, Summary: "finding", Help: "help"})
	n := 0
	for _, d := range ds {
		if d.Code == code {
			n++
		}
	}
	if (n > 0) != (i == 0) {
		t.Fatalf("case %d: %v", i, ds)
	}
}

func TestWardleyUndefinedReferenceSpans(t *testing.T) {
	text := "wardley-beta\nevolve Gone 0.5\nMissing -> Other\n"
	src := []byte(text)
	ast, parsed := syn.Parse(src, syntax.Preprocess(src).Removed)
	if len(parsed) != 0 {
		t.Fatalf("parse: %v", parsed)
	}
	m, _ := wardley.Resolve(src, ast)
	ds := wardleyRule(m, Row{Code: "wardley/undefined-component", Summary: "finding"})
	want := []string{"Missing", "Other", "Gone"}
	if len(ds) != len(want) {
		t.Fatalf("diagnostics: %v", ds)
	}
	for i, d := range ds {
		if got := text[d.Span.Start:d.Span.End]; got != want[i] {
			t.Fatalf("reference %d: got %q, want %q", i, got, want[i])
		}
	}
}
