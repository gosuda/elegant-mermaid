package scene

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func frameDump() Dump {
	return Dump{
		Kind:    "flowchart",
		Options: DefaultOptions(),
		Canvas:  geom.Size{W: 100, H: 100},
		Boxes: []Box{
			{ID: "G", Role: RoleGroup, Rect: geom.Rect{X: 0, Y: 0, W: 40, H: 40}},
			{ID: "N", Role: RoleNode, Rect: geom.Rect{X: 5, Y: 5, W: 10, H: 10}, Parent: "G", Exclusive: true},
			{ID: "F", Role: RoleNode, Rect: geom.Rect{X: 60, Y: 0, W: 10, H: 10}, Exclusive: true},
		},
	}
}

func withLabel(d Dump, r geom.Rect) Dump {
	d.Labels = []Label{{ID: "l", Owner: "N", Rect: r}}
	return d
}

func TestFrameClearanceClause(t *testing.T) {
	cases := []struct {
		name   string
		change func(*Dump)
		holds  bool
	}{
		{"members and distant boxes", func(*Dump) {}, true},
		{"foreign node overlaps the frame", func(d *Dump) { d.Boxes[2].Rect = geom.Rect{X: 30, Y: 30, W: 20, H: 20} }, false},
		{"foreign node touches the frame", func(d *Dump) { d.Boxes[2].Rect = geom.Rect{X: 40, Y: 0, W: 10, H: 10} }, true},
		{"foreign node inside the frame", func(d *Dump) { d.Boxes[2].Rect = geom.Rect{X: 20, Y: 20, W: 10, H: 10} }, false},
		{"sibling frame overlaps", func(d *Dump) {
			d.Boxes = append(d.Boxes, Box{ID: "H", Role: RoleGroup, Rect: geom.Rect{X: 30, Y: 0, W: 40, H: 40}})
		}, false},
		{"sibling frame is disjoint", func(d *Dump) {
			d.Boxes = append(d.Boxes, Box{ID: "H", Role: RoleGroup, Rect: geom.Rect{X: 40, Y: 0, W: 20, H: 40}})
		}, true},
		{"nested frame is contained", func(d *Dump) {
			d.Boxes = append(d.Boxes, Box{ID: "H", Role: RoleGroup, Rect: geom.Rect{X: 2, Y: 2, W: 30, H: 30}, Parent: "G"})
			d.Boxes[1].Parent = "H"
		}, true},
		{"frame overlaps the nested frame of another frame", func(d *Dump) {
			d.Boxes = append(d.Boxes,
				Box{ID: "P", Role: RoleGroup, Rect: geom.Rect{X: 30, Y: 30, W: 60, H: 60}},
				Box{ID: "Q", Role: RoleGroup, Rect: geom.Rect{X: 35, Y: 35, W: 20, H: 20}, Parent: "P"})
		}, false},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			d := frameDump()
			c.change(&d)
			clause, failed, err := d.Validate()
			if err != nil {
				t.Fatal(err)
			}
			if c.holds && failed || !c.holds && (!failed || clause != ClauseFrameClearance) {
				t.Fatalf("clause %+v failed %v", clause, failed)
			}
		})
	}
}

func TestFrameClearanceLabels(t *testing.T) {
	cases := []struct {
		name string
		rect geom.Rect
		want Clause
	}{
		{"strictly inside", geom.Rect{X: 10, Y: 20, W: 10, H: 5}, Clause{}},
		{"disjoint", geom.Rect{X: 60, Y: 50, W: 5, H: 5}, Clause{}},
		{"touches the frame from outside", geom.Rect{X: 40, Y: 20, W: 10, H: 5}, Clause{}},
		{"straddles the right border", geom.Rect{X: 35, Y: 20, W: 10, H: 5}, ClauseFrameClearance},
		{"touches the left border from inside", geom.Rect{X: 0, Y: 20, W: 10, H: 5}, ClauseFrameClearance},
		{"touches the bottom border from inside", geom.Rect{X: 10, Y: 35, W: 10, H: 5}, ClauseFrameClearance},
		{"covers a member", geom.Rect{X: 0, Y: 0, W: 50, H: 50}, ClauseLabelClearance},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			d := withLabel(frameDump(), c.rect)
			clause, failed, err := d.Validate()
			if err != nil || failed != (c.want != Clause{}) || clause != c.want {
				t.Fatalf("clause %+v failed %v err %v", clause, failed, err)
			}
		})
	}
}

func TestFrameClearanceFollowsLabelClearance(t *testing.T) {
	d := withLabel(frameDump(), geom.Rect{X: 36, Y: 36, W: 10, H: 10})
	d.Boxes[2].Rect = geom.Rect{X: 36, Y: 36, W: 10, H: 10}
	clause, failed, err := d.Validate()
	if err != nil || !failed || clause != ClauseLabelClearance {
		t.Fatalf("clause %+v failed %v err %v", clause, failed, err)
	}
	if ClauseFrameClearance.ID != "frame-clearance" || ClauseFrameClearance.Message != "group frame overlaps a foreign box or label" {
		t.Fatalf("clause text %+v", ClauseFrameClearance)
	}
}
