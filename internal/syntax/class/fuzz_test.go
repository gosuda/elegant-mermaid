package class_test

import (
	"testing"

	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func FuzzClass(f *testing.F) {
	for _, s := range []string{"classDiagram\nclass A", "classDiagram\nA <|-- B : inherits", "classDiagram\nnamespace N {\nclass A {\n+run()\n}\n}", "classDiagram\nnote \"text\"", "classDiagram\nclick A call f(\"x\")"} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, src []byte) {
		_, ds := parser.Parse(src, nil)
		for _, d := range ds {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
				t.Fatal(d)
			}
		}
	})
}
