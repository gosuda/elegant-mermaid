package layout

import (
	"bytes"
	"errors"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
)

func TestGeneratedRouteIDsAvoidBoxes(t *testing.T) {
	source := []byte("flowchart\ne0[Node] --> A\nsubgraph e1[Group]\nB\nend\nA --> B\n")
	in, accepted := inputSource(t, source)
	if !accepted {
		t.Fatal("collision fixture rejected")
	}
	if len(in.Routes) != 2 {
		t.Fatal(in.Routes)
	}
	if in.Routes[0].ID != "e2" || in.Routes[1].ID != "e3" {
		t.Fatal("route ordinal must skip node and group identifiers", in.Routes)
	}
	step14Scene(t, in)
}
func ambiguousOwnerInput() Input {
	in := step14Input()
	in.Boxes[0].ID = "e0"
	in.Routes[0].From = "e0"
	in.Labels = []Label{{ID: "ambiguous.label", Owner: "e0", Text: "ambiguous"}}
	return in
}
func TestDirectLayoutRejectsAmbiguousOwners(t *testing.T) {
	_, _, err := Layout(ambiguousOwnerInput())
	if !errors.Is(err, layered.ErrGraph) {
		t.Fatalf("ambiguous direct input accepted: %v", err)
	}
}
func TestModelWriterRejectsAmbiguousOwners(t *testing.T) {
	var out bytes.Buffer
	err := WriteModelDump(&out, ambiguousOwnerInput())
	if !errors.Is(err, layered.ErrGraph) || out.Len() != 0 {
		t.Fatalf("ambiguous model emitted: %v %s", err, out.Bytes())
	}
}
