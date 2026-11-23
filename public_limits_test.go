package mermaid_test

import (
	"fmt"
	"strings"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
)

func TestPublicFlowchartNestingLimit(t *testing.T) {
	for _, depth := range []int{63, 64, 65, 1024} {
		var source strings.Builder
		source.WriteString("flowchart LR\n")
		for level := range depth {
			fmt.Fprintf(&source, "subgraph S%d\n", level)
		}
		source.WriteString("A\n")
		source.WriteString(strings.Repeat("end\n", depth))
		document := mermaid.Parse([]byte(source.String()))
		diagnostics := document.Diagnostics()
		if depth <= 64 {
			if len(diagnostics) != 0 {
				t.Fatalf("depth %d: valid nesting rejected: %+v", depth, diagnostics)
			}
			continue
		}
		if !document.HasErrors() || len(diagnostics) != 1 {
			t.Fatalf("depth %d: want one nesting error, got %+v", depth, diagnostics)
		}
		diagnostic := diagnostics[0]
		start := strings.Index(source.String(), "subgraph S64\n")
		wantSpan := mermaid.Span{Start: start, End: start + len("subgraph")}
		if diagnostic.Code != "limit/nesting-depth" || diagnostic.Span != wantSpan {
			t.Fatalf("depth %d: nesting boundary diagnostic: %+v", depth, diagnostic)
		}
	}
}
