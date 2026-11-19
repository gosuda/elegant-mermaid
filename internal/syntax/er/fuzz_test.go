package er

import "testing"

func FuzzEr(f *testing.F) {
	for _, s := range []string{
		"erDiagram\nA ||--o{ B : has",
		"erDiagram\nA {\nstring name PK \"the name\"\n}",
		"erDiagram\nA[\"é\"]:::red ||..o{ B : r",
		"erDiagram\nsubgraph S[Title]\nA\nend",
		"erDiagram\nclassDef red fill:#f00,color:#0f0\nclass A red",
		"erDiagram\naccTitle: t\naccDescr {multi\nline}",
	} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, src []byte) {
		_, ds := Parse(src, nil)
		for _, d := range ds {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
				t.Fatal(d)
			}
		}
	})
}
