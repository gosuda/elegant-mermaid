package layered

import (
	"errors"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestLimitsPrecedeGraphResolution(t *testing.T) {
	in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "A"}, {ID: "B"}}, Routes: []scene.Route{{ID: "e0", From: "missing", To: "B"}}}
	opts := scene.DefaultOptions()
	opts.Limits.MaxNodes = 1
	_, err := LayoutFamily(in, Options{Scene: opts})
	limit, ok := errors.AsType[*LimitError](err)
	if !ok || limit.Resource != "nodes" || limit.Actual != 2 || limit.Limit != 1 {
		t.Fatalf("limit must precede missing endpoint: %v", err)
	}
}
func TestTextBudgetCountsOwnedResolvedText(t *testing.T) {
	in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "fallback"}, {ID: "group", Role: scene.RoleGroup}}, Text: []string{"fallback", "Group"}, Labels: []scene.Label{{ID: "label", Owner: "edge", Text: "é"}}}
	in.Routes = []scene.Route{{ID: "edge", From: "fallback", To: "fallback"}}
	in.Labels = append(in.Labels, scene.Label{ID: "group.label", Owner: "group", Text: "Group"})
	n, err := inputTextBytes(in)
	if err != nil {
		t.Fatal(err)
	}
	if n != 15 {
		t.Fatalf("8 fallback bytes +5 title bytes +2 UTF8 edge label bytes=15; got %d", n)
	}
	opts := scene.DefaultOptions()
	opts.Limits.MaxTextBytes = 15
	if err := enforceLimits(in, opts); err != nil {
		t.Fatal(err)
	}
	opts.Limits.MaxTextBytes = 14
	if !errors.Is(enforceLimits(in, opts), ErrTooLarge) {
		t.Fatal("one-over text budget accepted")
	}
}
