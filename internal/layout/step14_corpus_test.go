package layout

import (
	"os"
	"path/filepath"
	"strconv"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
	random "github.com/gosuda/elegant-mermaid/tools/randgraph/gen"
)

func TestRandomCompoundLayeredValidity(t *testing.T) {
	for seed := range 200 {
		source, err := random.Source("layered", seed)
		if err != nil {
			t.Fatal(err)
		}
		in := randomInput(source)
		for i := range in.Boxes {
			in.Boxes[i].Parent = "G" + strconv.Itoa(i%2)
		}
		in.Boxes = append(in.Boxes, Box{ID: "G0", Role: scene.RoleGroup, Parent: "outer"}, Box{ID: "G1", Role: scene.RoleGroup, Parent: "outer"}, Box{ID: "outer", Role: scene.RoleGroup})
		in.Groups = []Group{{ID: "G0"}, {ID: "G1"}, {ID: "outer"}}
		in.Labels = append(in.Labels, Label{ID: "G0.label", Owner: "G0", Text: "Left"}, Label{ID: "G1.label", Owner: "G1", Text: "Right"}, Label{ID: "outer.label", Owner: "outer", Text: "Outer"})
		for i, r := range in.Routes {
			if i%3 == 0 {
				in.Labels = append(in.Labels, Label{ID: r.ID + ".label", Owner: r.ID, Text: "yes"})
			}
		}
		in.Routes = append(in.Routes, Route{ID: "loop", From: in.Boxes[0].ID, To: in.Boxes[0].ID, Orthogonal: true})
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in.Profile = profile
			for _, direction := range []scene.Direction{scene.DirectionTB, scene.DirectionBT, scene.DirectionLR, scene.DirectionRL} {
				in.Direction = direction
				assertValidLayout(t, seed, in)
			}
		}
	}
}

func TestAcceptedFlowchartCorpusLayouts(t *testing.T) {
	accepted := 0
	err := filepath.WalkDir("../../corpus/flowchart", func(path string, entry os.DirEntry, walkErr error) error {
		if walkErr != nil {
			return walkErr
		}
		if entry.IsDir() || filepath.Ext(path) != ".mmd" {
			return nil
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		in, ok := inputSource(t, data)
		if !ok {
			return nil
		}
		accepted++
		t.Run(path, func(t *testing.T) {
			for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
				in.Profile = profile
				step14Scene(t, in)
			}
		})
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if accepted == 0 {
		t.Fatal("corpus contained no accepted flowcharts")
	}
	t.Logf("accepted flowcharts validated in both profiles: %d", accepted)
}
