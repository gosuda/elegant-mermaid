package flowchart

import (
	"testing"
	"unicode/utf8"
)

func FuzzFlowchart(f *testing.F) {
	for _, s := range []string{"flowchart LR\nA --> B\n", "flowchart LR\nA[Start --> B\n", "flowchart TD\nA((text))\n"} {
		f.Add(s)
	}
	f.Fuzz(func(t *testing.T, s string) {
		if !utf8.ValidString(s) {
			t.Skip()
		}
		_, diagnostics := Parse([]byte(s), nil)
		for _, d := range diagnostics {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(s) {
				t.Fatalf("invalid span: %+v", d)
			}
		}
	})
}
