package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func groupRouteInput() Input {
	return Input{Kind: "flowchart", Profile: scene.ProfileCell, Options: scene.DefaultOptions(), Boxes: []Box{
		{ID: "S", Role: scene.RoleGroup, Direction: "LR"}, {ID: "A", Parent: "S", Exclusive: true}, {ID: "B", Parent: "S", Exclusive: true}, {ID: "X", Exclusive: true},
	}, Groups: []Group{{ID: "S"}}, Labels: []Label{{ID: "S.label", Owner: "S", Text: "S"}}, Routes: []Route{{ID: "inside", From: "A", To: "B", Orthogonal: true}}}
}
func TestGroupBoundaryRoutesPreserveIdentity(t *testing.T) {
	cases := []struct {
		name, from, to string
		ignored        bool
	}{
		{"entry", "S", "A", true}, {"exit", "A", "S", true}, {"external", "S", "X", false}, {"self", "S", "S", false},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			in := groupRouteInput()
			in.Routes = append(in.Routes, Route{ID: "boundary", From: c.from, To: c.to, Orthogonal: true})
			s, ds, err := Layout(in)
			if err != nil {
				t.Fatal(err)
			}
			assertGroupRouteIdentity(t, s)
			ignored := false
			for _, d := range ds {
				ignored = ignored || d.Code == "flowchart/subgraph-direction-ignored"
			}
			if ignored != c.ignored {
				t.Fatal("boundary ownership changed direction policy", ds)
			}
		})
	}
}

func assertGroupRouteIdentity(t *testing.T, s scene.Scene) {
	t.Helper()
	clause, failed, err := s.Validate()
	if failed || err != nil {
		t.Fatalf("%v: %v", clause, err)
	}
	if len(s.Boxes) != 4 || len(s.Routes) != 2 {
		t.Fatal("recursive layout changed identity count", s.Boxes, s.Routes)
	}
	if s.Routes[0].ID != "inside" || s.Routes[1].ID != "boundary" || len(s.Routes[1].Points) == 0 {
		t.Fatal("route dropped or duplicated", s.Routes)
	}
}
func TestNestedGroupProxyRoutes(t *testing.T) {
	in := groupRouteInput()
	in.Boxes[0].Direction = ""
	in.Boxes = append(in.Boxes, Box{ID: "outer", Role: scene.RoleGroup})
	in.Boxes[0].Parent = "outer"
	in.Groups = append(in.Groups, Group{ID: "outer"})
	in.Labels = append(in.Labels, Label{ID: "outer.label", Owner: "outer", Text: "Outer"})
	in.Routes = append(in.Routes, Route{ID: "nested-entry", From: "outer", To: "A", Orthogonal: true}, Route{ID: "nested-exit", From: "B", To: "outer", Orthogonal: true}, Route{ID: "external", From: "S", To: "X", Orthogonal: true})
	for _, p := range []scene.Profile{scene.ProfileCell, scene.ProfileVector} {
		in.Profile = p
		step14Scene(t, in)
	}
}
