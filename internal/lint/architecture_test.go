package lint

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	"github.com/gosuda/elegant-mermaid/internal/source"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/architecture"
)

func TestArchitectureConsumerRules(t *testing.T) {
	for _, tc := range []struct {
		code, source string
		want         int
	}{
		{"architecture/no-elements", "architecture-beta\n", 1},
		{"architecture/no-elements", "architecture-beta\nservice a(server)\n", 0},
		{"architecture/no-edges", "architecture-beta\nservice a(server)\n", 1},
		{"architecture/no-edges", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\n", 0},
		{"architecture/duplicate-edge", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\na:R -- L:b\n", 1},
		{"architecture/duplicate-edge", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\na:L -- R:b\n", 0},
		{"architecture/no-elements", "architecture-beta\nservice a(server) in missing\n", 0},
		{"architecture/no-edges", "architecture-beta\nservice a(server) in missing\n", 1},
		{"architecture/no-edges", "architecture-beta\nservice a(server)\na:R -- L:missing\n", 0},
		{"architecture/duplicate-edge", "architecture-beta\na:R -- L:b\na:R -- L:b\n", 1},
		{"architecture/duplicate-edge", "architecture-beta\nservice a(server)\nservice b(server)\na:R -- L:b\nb:L -- R:a\n", 0},
	} {
		checkArchitectureConsumerCase(t, tc.code, tc.source, tc.want)
	}
}

func checkArchitectureConsumerCase(t *testing.T, code, text string, want int) {
	t.Helper()
	document, parsed := parser.Parse([]byte(text), nil)
	if len(parsed) != 0 {
		t.Fatalf("parse diagnostics: %+v", parsed)
	}
	m, _ := model.Resolve([]byte(text), document)
	row := Row{Code: code, Summary: "expected", Help: "help"}
	predicates := map[string]func(*model.Model, Row) []diag.Diagnostic{
		"architecture/no-elements":    architectureNoElements,
		"architecture/no-edges":       architectureNoEdges,
		"architecture/duplicate-edge": architectureDuplicateEdge,
	}
	result := predicates[code](m, row)
	count := 0
	for _, d := range result {
		if d.Code != code {
			continue
		}
		count++
		checkArchitectureFinding(t, d, text, document.Header.Span)
	}
	if count != want {
		t.Fatalf("%s on %q: got %d want %d", code, text, count, want)
	}
}

func checkArchitectureFinding(t *testing.T, d diag.Diagnostic, text string, header source.Span) {
	t.Helper()
	if d.Message == "" || d.Help == "" || d.Span.Start < 0 || d.Span.End > len(text) {
		t.Fatalf("invalid finding: %+v", d)
	}
	if d.Code == "architecture/duplicate-edge" {
		if d.Span.Start != strings.LastIndex(text, "a:R -- L:b") {
			t.Fatalf("wrong duplicate statement span: %+v", d.Span)
		}
		return
	}
	if d.Span != header {
		t.Fatalf("wrong header span: %+v", d.Span)
	}
}
