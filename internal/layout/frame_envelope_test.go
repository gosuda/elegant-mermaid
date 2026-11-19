package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const frameEnvelopeSource = "flowchart BT\nsubgraph G0\nn5\nn0\nn7\nend\nn6 -->|l| n7\nn3 --> n7\nG0 --> G0\n"

func TestFrameEnvelopeKeepsForeignBoxesOutsideFrames(t *testing.T) {
	in, ok := inputSource(t, []byte(frameEnvelopeSource))
	if !ok {
		t.Fatal("fixture rejected")
	}
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in.Profile = profile
		s := step14Scene(t, in)
		clause, failed, err := s.Validate()
		if err != nil || failed {
			t.Fatalf("%v: clause %+v failed %v err %v", profile, clause, failed, err)
		}
	}
}
