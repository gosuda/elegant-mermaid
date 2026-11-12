package layout

import (
	"bytes"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestGroupModelTransport(t *testing.T) {
	in := Input{Kind: "flowchart", Options: scene.DefaultOptions(), Boxes: []Box{{ID: "G", Role: scene.RoleGroup, Direction: "LR"}, {ID: "A", Parent: "G", Exclusive: true}}, Labels: []Label{{ID: "G.label", Owner: "G", Text: "Title"}}}
	dump := dumpInput(t, in)
	if !bytes.Contains(dump, []byte(`{"id":"G","role":"group","parent":"","exclusive":false,"direction":"LR"}`)) {
		t.Fatalf("group direction is absent from model relation: %s", dump)
	}
	if !bytes.Contains(dump, []byte(`{"id":"G.label","owner":"G","text":"Title","lines":[]}`)) {
		t.Fatalf("group title is absent from model labels: %s", dump)
	}
	in.Boxes[0].Direction = ""
	in.Labels[0].Text = ""
	dump = dumpInput(t, in)
	if !bytes.Contains(dump, []byte(`"exclusive":false,"direction":""`)) || !bytes.Contains(dump, []byte(`"owner":"G","text":"","lines":[]`)) {
		t.Fatalf("explicit empty values lost: %s", dump)
	}
}
func TestGroupDirectionIsModelOnly(t *testing.T) {
	in := groupRouteInput()
	s := step14Scene(t, in)
	data := s.AppendJSON(nil)
	if bytes.Contains(data, []byte(`"exclusive":false,"direction":`)) {
		t.Fatalf("model-only relation leaked into layout dump: %s", data)
	}
}
