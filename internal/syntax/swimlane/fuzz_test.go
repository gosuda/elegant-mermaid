package swimlane

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

func FuzzSwimlane(f *testing.F) {
	for _, s := range []string{
		"swimlane-beta LR\n  subgraph Customer\n    Browse[Browse] --> Pay[Pay]\n  end\n",
		"swimlane-beta TB\n  subgraph A\n    x\n  end\n  subgraph B\n    y\n  end\n  x --> y\n",
		"swimlane-beta\n  subgraph A\n    subgraph Inner\n      n\n    end\n  end\n  n --> m\n",
		"swimlane-beta LR\n  A[Start --> B\n",
		"swimlane-beta LR\n  A -> B\n",
		"swimlane-beta XX\n  subgraph\n",
		"swimlane-beta\n  end\n  click A href \"https://example.com\"\n  linkStyle 3 stroke:#f00\n",
		"swimlane-beta TD\n  A@{ shape: nope }\n",
		"",
	} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, src []byte) {
		file, diagnostics := Parse(src, nil)
		if file == nil {
			t.Fatal("nil file")
		}
		for _, d := range diagnostics {
			if d.Span.Start < 0 || d.Span.End < d.Span.Start || d.Span.End > len(src) {
				t.Fatalf("invalid span: %+v", d)
			}
			if name, ok := strings.CutPrefix(d.Code, flowchartPrefix); ok && hasRow(swimlanePrefix+name) {
				t.Fatalf("diagnostic %q kept the flowchart prefix", d.Code)
			}
		}
	})
}

func hasRow(code string) bool {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return true
		}
	}
	return false
}
