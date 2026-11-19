package flowchart

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

func TestShapeDataConfigSpansStayInsideTheBody(t *testing.T) {
	for _, c := range []struct {
		name string
		src  string
		want source.Span
	}{
		{"unterminated body at end of input", "flowchart TD\n  G@{ s", source.Span{Start: 20, End: 20}},
		{"collection left open before the closing brace", "flowchart TD\n  G@{ a: [ }\n", source.Span{Start: 24, End: 24}},
		{"inner brace closes the wrapped mapping", "flowchart TD\n  G@{ a: {b: }\n", source.Span{Start: 26, End: 26}},
		{"quoted string runs to the end of input", "flowchart TD\n  G@{ a: \"x }\n", source.Span{Start: 27, End: 27}},
		{"error inside a terminated body", "flowchart TD\n  G@{ - }\n", source.Span{Start: 19, End: 20}},
	} {
		src := []byte(c.src)
		ast, _ := syn.Parse(src, nil)
		_, diagnostics := Resolve(src, ast)
		var spans []source.Span
		for _, d := range diagnostics {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
				t.Fatalf("%s: span %v leaves the %d-byte source: %+v", c.name, d.Span, len(src), d)
			}
			if d.Code == codeMalformedConfig {
				spans = append(spans, d.Span)
			}
		}
		if len(spans) != 1 || spans[0] != c.want {
			t.Fatalf("%s: %s spans %v, want [%v]", c.name, codeMalformedConfig, spans, c.want)
		}
	}
}

func TestShapeDataNewlineBeforeValueSpan(t *testing.T) {
	for _, text := range []string{
		"flowchart\nA@{\n shape:\n  missing\n}\n",
		"flowchart\r\nA@{\r\n shape:\r\n  missing\r\n}\r\n",
		"flowchart\rA@{\r shape:\r  missing\r}\r",
	} {
		src := []byte(text)
		ast, syntaxDiagnostics := syn.Parse(src, nil)
		if len(syntaxDiagnostics) != 0 {
			t.Fatal(syntaxDiagnostics)
		}
		_, diagnostics := Resolve(src, ast)
		if len(diagnostics) != 1 {
			t.Fatalf("expected one unsupported-shape diagnostic, got %v", diagnostics)
		}
		d := diagnostics[0]
		if d.Code != "flowchart/typed-shape-unsupported" || string(src[d.Span.Start:d.Span.End]) != "missing" {
			t.Fatalf("unexpected shape value diagnostic: %v", d)
		}
	}
}
