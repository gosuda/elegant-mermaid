package lint

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/model/quadrant"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/quadrant"
)

func TestQuadrantRules(t *testing.T) {
	cases := []struct{ code, bad, good string }{
		{"quadrant/duplicate-point", "quadrantChart\nA: [0.2, 0.3]\nA: [0.4, 0.5]\n", "quadrantChart\nA: [0.2, 0.3]\nB: [0.4, 0.5]\n"},
		{"quadrant/no-points", "quadrantChart\nquadrant-1 Good\n", "quadrantChart\nquadrant-1 Good\nA: [0.2, 0.3]\n"},
		{"quadrant/missing-x-axis", "quadrantChart\nA: [0.2, 0.3]\n", "quadrantChart\nx-axis Low --> High\nA: [0.2, 0.3]\n"},
		{"quadrant/missing-y-axis", "quadrantChart\nA: [0.2, 0.3]\n", "quadrantChart\ny-axis Low --> High\nA: [0.2, 0.3]\n"},
		{"quadrant/duplicate-quadrant", "quadrantChart\nquadrant-1 Good\nquadrant-1 Better\n", "quadrantChart\nquadrant-1 Good\nquadrant-2 Better\n"},
		{"quadrant/no-points", "quadrantChart\nx-axis Low\n", "quadrantChart\ntitle Only title\n"},
		{"quadrant/no-points", "quadrantChart\ny-axis Low\n", "quadrantChart\n"},
	}
	for _, c := range cases {
		t.Run(c.code, func(t *testing.T) {
			for i, text := range []string{c.bad, c.good} {
				checkQuadrantRuleCase(t, c.code, text, i)
			}
		})
	}
}

func checkQuadrantRuleCase(t *testing.T, code, text string, i int) {
	t.Helper()
	src := []byte(text)
	file, parseDiagnostics := parser.Parse(src, syntax.Preprocess(src).Removed)
	if len(parseDiagnostics) != 0 {
		t.Fatalf("parse: %v", parseDiagnostics)
	}
	m, modelDiagnostics := quadrant.Resolve(src, file)
	if len(modelDiagnostics) != 0 {
		t.Fatalf("resolve: %v", modelDiagnostics)
	}
	ds := quadrantRule(m, Row{Code: code, Summary: "finding", Help: "help"})
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

func TestQuadrantDuplicatePointRawKeysAndSpans(t *testing.T) {
	text := "quadrantChart\nA: [0.2, 0.3]\nA: [0.4, 0.5]\nA: [0.6, 0.7]\n"
	src := []byte(text)
	file, ds := parser.Parse(src, syntax.Preprocess(src).Removed)
	if len(ds) != 0 {
		t.Fatalf("parse: %v", ds)
	}
	m, ds := quadrant.Resolve(src, file)
	if len(ds) != 0 {
		t.Fatalf("resolve: %v", ds)
	}
	findings := quadrantRule(m, Row{Code: "quadrant/duplicate-point"})
	if len(findings) != 2 {
		t.Fatalf("findings: %v", findings)
	}
	for i, start := range []int{28, 42} {
		if findings[i].Span.Start != start || findings[i].Span.End != start+1 {
			t.Fatalf("finding %d: %v", i, findings[i])
		}
	}
}
