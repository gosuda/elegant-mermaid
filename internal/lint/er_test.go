package lint

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/er"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/er"
)

func TestErLintRules(t *testing.T) {
	cases := []struct{ code, trigger, clean string }{
		{"er/duplicate-attribute", "erDiagram\nA {\nint id\nstring id\n}\n", "erDiagram\nA {\nint id\nstring name\n}\n"},
		{"er/duplicate-entity", "erDiagram\nA {\nint id\n}\nA {\nint name\n}\n", "erDiagram\nA {\nint id\n}\nB {\nint name\n}\n"},
		{"er/duplicate-attribute", "erDiagram\nA {\nint id\nint id\n}\nA {\nint id\n}\n", "erDiagram\nA {\nint id\n}\nA {\nint id\n}\n"},
		{"er/duplicate-entity", "erDiagram\nA\nA {\n}\nA {\n}\n", "erDiagram\nA\nA {\n}\n"},
		{"er/standalone-entity", "erDiagram\nA {\nint id\n}\n", "erDiagram\nA {\nint id\n}\nA ||--|| B : owns\n"},
	}
	for _, tc := range cases {
		t.Run(tc.code, func(t *testing.T) {
			row := Row{Code: tc.code, Summary: "finding", Help: "help"}
			for _, input := range []struct {
				source string
				want   int
			}{{tc.trigger, 1}, {tc.clean, 0}} {
				checkErRuleCase(t, tc.code, input.source, input.want, row)
			}
		})
	}
}

func checkErRuleCase(t *testing.T, code, text string, want int, row Row) {
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
	rule := map[string]func(*model.Model, Row) []diag.Diagnostic{
		"er/duplicate-attribute": ERDuplicateAttribute,
		"er/duplicate-entity":    ERDuplicateEntity,
		"er/standalone-entity":   ERStandaloneEntity,
	}[code]
	got := rule(m, row)
	if len(got) != want {
		t.Fatalf("%s: got %d findings, want %d", text, len(got), want)
	}
	for _, d := range got {
		checkErFinding(t, d, code, text)
	}
}

func checkErFinding(t *testing.T, d diag.Diagnostic, code, text string) {
	t.Helper()
	if d.Code != code || d.Message != "finding" || d.Help != "help" || d.Span.Start < 0 || d.Span.End > len(text) || d.Span.End <= d.Span.Start {
		t.Fatalf("bad diagnostic: %+v", d)
	}
}

func TestERDeclarationOrderAndRelationshipScope(t *testing.T) {
	text := "erDiagram\nA\nsubgraph G\nA {\nint id\nint id\n}\nend\nA {\nint id\n}\nA {\n}\nG ||--|| A : owns\n"
	src := []byte(text)
	parsed, diagnostics := syn.Parse(src, nil)
	if len(diagnostics) != 0 {
		t.Fatalf("parse diagnostics: %+v", diagnostics)
	}
	m, diagnostics := model.Resolve(src, parsed)
	if len(diagnostics) != 0 {
		t.Fatalf("resolve diagnostics: %+v", diagnostics)
	}
	attributes := ERDuplicateAttribute(m, Row{Code: "er/duplicate-attribute"})
	if len(attributes) != 1 || attributes[0].Span.Start != strings.Index(text, "id\nint id")+7 {
		t.Fatalf("duplicate attribute spans: %+v", attributes)
	}
	entities := ERDuplicateEntity(m, Row{Code: "er/duplicate-entity"})
	second := strings.Index(text, "end\nA {") + 4
	third := strings.LastIndex(text, "A {")
	if len(entities) != 2 || entities[0].Span.Start != second || entities[1].Span.Start != third {
		t.Fatalf("duplicate entity order: %+v", entities)
	}
	if got := ERStandaloneEntity(m, Row{Code: "er/standalone-entity"}); len(got) != 0 {
		t.Fatalf("relationship endpoint ignored: %+v", got)
	}
}
