package agentflow

import (
	"testing"

	synagentflow "github.com/gosuda/elegant-mermaid/internal/syntax/agentflow"
)

func TestResolveSeeds(t *testing.T) {
	for _, src := range []string{
		"agentflow-beta\nt1@{shape: task}\nt2@{shape: tool}\ni3@{shape: input}\nd4@{shape: decision}\nt1 --> t2\n",
		"agentflow-beta LR\nflow main\na\nflow sub\nb\nend\nb --> a\nend\n",
		"agentflow-beta\na@{shape: diamond, label: \"pick\"}\nclass a big\nclassDef big fill:#123\n",
		"agentflow-beta\nglobal\ng1\nend\nflow f1\nf2 --> g1\nlinkStyle 0 fill:blue\nend\n",
		"agentflow-beta TB\nflow g[\"Review\"]\n  c[\"changes\"]@{ shape: input }\n  c --> g\nend\n",
	} {
		start, parseDiags := synagentflow.Parse([]byte(src), nil)
		if len(parseDiags) != 0 {
			t.Fatalf("parse %q: %v", src, parseDiags)
		}
		model, diags := Resolve([]byte(src), start)
		if model == nil {
			t.Fatalf("nil model for %q", src)
		}
		for _, d := range diags {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
				t.Fatalf("span %q: %v", src, d)
			}
		}
	}
}

func TestResolveCollapseRedirectsEdges(t *testing.T) {
	src := "agentflow-beta\nflow outer@{view: collapsed}\nflow inner\na\nend\nend\nb\na --> b\n"
	start, parseDiags := synagentflow.Parse([]byte(src), nil)
	if len(parseDiags) != 0 {
		t.Fatalf("parse: %v", parseDiags)
	}
	model, _ := Resolve([]byte(src), start)
	if len(model.Edges) != 1 {
		t.Fatalf("edges: %#v", model.Edges)
	}
	if model.Edges[0].From != "outer" || model.Edges[0].To != "b" {
		t.Fatalf("redirect: %#v", model.Edges[0])
	}
}
