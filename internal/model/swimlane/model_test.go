package swimlane

import (
	"slices"
	"testing"

	swimlaneparser "github.com/gosuda/elegant-mermaid/internal/syntax/swimlane"
)

func lanes(t *testing.T, src string) []string {
	t.Helper()
	file, parsed := swimlaneparser.Parse([]byte(src), nil)
	if len(parsed) != 0 {
		t.Fatalf("%+v", parsed)
	}
	m, resolved := Resolve([]byte(src), file)
	if len(resolved) != 0 {
		t.Fatalf("%+v", resolved)
	}
	return m.Lanes()
}

func TestLanesFollowFirstOpeningOrder(t *testing.T) {
	got := lanes(t, "swimlane-beta LR\n  subgraph B\n    b\n  end\n  subgraph A\n    a\n  end\n  subgraph C\n  end\n")
	if want := []string{"B", "A", "C"}; !slices.Equal(got, want) {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func TestNestedSubgraphIsNotALane(t *testing.T) {
	got := lanes(t, "swimlane-beta LR\n  subgraph A\n    subgraph Inner\n      n\n    end\n  end\n")
	if want := []string{"A"}; !slices.Equal(got, want) {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func TestNodesOutsideLanesCreateNoLane(t *testing.T) {
	if got := lanes(t, "swimlane-beta LR\n  a --> b\n"); len(got) != 0 {
		t.Fatalf("got %v", got)
	}
}
