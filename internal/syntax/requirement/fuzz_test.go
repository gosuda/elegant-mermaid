package requirement

import (
	"testing"
)

func FuzzRequirement(f *testing.F) {
	for _, s := range []string{
		"requirementDiagram\nrequirement r {\nid: 1\ntext: t\nrisk: high\nverifyMethod: test\n}\nelement e {\ntype: simulation\n}\ne - satisfies -> r\n",
		"requirementDiagram\nA <- contains - B\nstyle A fill:#abc\nclassDef blue fill:#abc,color:red;\nclass A,B blue\nA:::blue\n",
		"requirement\r\naccDescr {multi\r\nline}\r\n",
		"requirementDiagram\nfunctionalRequirement f:::blue {\n}\n",
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
