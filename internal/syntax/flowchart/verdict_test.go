package flowchart

import "testing"

func TestUpstreamAcceptedSyntax(t *testing.T) {
	for _, src := range []string{
		"flowchart\n A@{ shape: rect, label: \"process\" }\n",
		"flowchart TD\nA{{choice}} --> B((circle))\n",
		"flowchart TD\nA:::classA --> B:::classB\nclassDef classA fill:red\n",
		"flowchart LR\nA e1@--> B\ne1@{ animate: true }\n",
		"flowchart LR\nA-->B\nclick A call callback() \"tip\"\n",
		"flowchart LR\nA[/red<br/>text/] --> B\n",
		"flowchart TD\nA[<img src=\"https://example.test/image.svg\"> more text]\n",
		"\n  flowchart LR\naccTitle: A title\naccDescr: A description\noutside --> subgraph1\n",
		"flowchart LR\nA --- B === C\n",
	} {
		_, diagnostics := Parse([]byte(src), nil)
		if len(diagnostics) != 0 {
			t.Errorf("%q: %+v", src, diagnostics)
		}
	}
}

func TestUpstreamRejectedSyntax(t *testing.T) {
	for _, src := range []string{
		"flowchart TD\nA[/dev/tty unavailable]\n",
		"flowchart TD\nA-->B\nlinkStyle 0:1 stroke:red\n",
		"flowchart TD\nsubgraph\nA-->B\nend\n",
		"flowchart TD\nA --|text \"quoted\"|--> B\n",
		"flowchart TD\nA-->B\nclick A call \"tip\"\n",
	} {
		_, diagnostics := Parse([]byte(src), nil)
		if len(diagnostics) == 0 {
			t.Errorf("accepted %q", src)
		}
	}
}
