package mermaid_test

import (
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
)

func TestErrorTexts(t *testing.T) {
	d := mermaid.Parse([]byte("flowchart LR\nA[Alpha] --> B[Beta]\n"))
	_, err := mermaid.Layout(t.Context(), d, mermaid.LayoutOptions{Limits: mermaid.Limits{MaxNodes: 1}})
	if err == nil || err.Error() != "model exceeds the limit of 1; actual 2" {
		t.Fatalf("model over a limit: %v", err)
	}
	if got := mermaid.ErrOverflow.Error(); got != "arithmetic overflow" {
		t.Fatalf("overflow sentinel: %q", got)
	}
}
