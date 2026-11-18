package agentflow

import (
	"testing"
)

func FuzzAgentflow(f *testing.F) {
	for _, s := range []string{
		"agentflow-beta\ntask t1\ntool t2\ninput i3\ndecision d4\nt1 --> t2: uses\nt2 --> d4: checks\n",
		"agentflow-beta LR\nflow main {\ntask a\nflow sub {\ntask b\n}\nb --> a\n}\nconnector c [hub]\na --> c\n",
		"agentflow-beta\nglobal {\ntask g1\n}\nflow f1 --> f2: label\nlinkStyle default stroke:red\nlinkStyle 0 fill:blue,interpolate basis\n",
		"agentflow-beta\ntask a@{shape: diamond, label: \"pick one\"}\nclass a big\nclassDef big fill:#123\nclick a href \"https://example.com\" \"docs\" _blank\nclick a call someFn(\"x\")\n",
		"agentflow-beta\ntask \"quoted id\" {\"x\"\n",
		"agentflow-beta\nA -->\nend\nstyle\n",
	} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, src []byte) {
		start, ds := Parse(src, nil)
		for _, d := range ds {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
				t.Fatal(d)
			}
		}
		if start == nil {
			t.Fatal("nil start")
		}
	})
}
