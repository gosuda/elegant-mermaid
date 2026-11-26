package layered

import (
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestStraightenObstaclesGroupRealNode(t *testing.T) {
	p := &Proper{Nodes: []ProperNode{
		{Node: Node{ID: "a", Role: scene.RoleNode}},
		{Node: Node{ID: "b", Role: scene.RoleNode}},
		{Node: Node{ID: "g", Role: scene.RoleGroup}},
		{Node: Node{ID: "du"}, Dummy: true},
		{Node: Node{ID: "lb"}, Label: &EdgeLabel{}},
		{Node: Node{ID: "bd", Border: BorderLeft}},
	}}
	boxes := []Box{
		{ID: "a", Role: scene.RoleNode, Rect: geom.Rect{X: 60, Y: 0, W: 80, H: 40}},
		{ID: "b", Role: scene.RoleNode, Rect: geom.Rect{X: 60, Y: 200, W: 80, H: 40}},
		{ID: "g", Role: scene.RoleGroup, Rect: geom.Rect{X: 80, Y: 100, W: 40, H: 40}},
		{ID: "o", Role: scene.RoleGroup, Rect: geom.Rect{X: 500, Y: 100, W: 40, H: 40}},
		{ID: "du", Role: scene.RoleGroup, Rect: geom.Rect{X: 500, Y: 200, W: 40, H: 40}},
		{ID: "lb", Role: scene.RoleGroup, Rect: geom.Rect{X: 500, Y: 300, W: 40, H: 40}},
		{ID: "bd", Role: scene.RoleGroup, Rect: geom.Rect{X: 500, Y: 400, W: 40, H: 40}},
		{ID: "n2", Role: scene.RoleNode, Rect: geom.Rect{X: 500, Y: 0, W: 40, H: 40}},
	}
	obstacles := straightenObstacles(p, boxes)
	var got []string
	for _, b := range obstacles {
		got = append(got, b.ID)
	}
	if want := []string{"a", "b", "g", "n2"}; !slices.Equal(got, want) {
		t.Fatalf("obstacles %v, want %v", got, want)
	}
	candidate := []geom.Point{{X: 100, Y: 40}, {X: 100, Y: 200}}
	clear, err := straightStepClearBoxes(obstacles, "a", "b", candidate)
	if err != nil {
		t.Fatal(err)
	}
	if clear {
		t.Fatal("corridor through group real node g must be declined")
	}
}
