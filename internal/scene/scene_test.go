package scene

import (
	"errors"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func TestModelGolden(t *testing.T) {
	d := Dump{Stage: StageModel, Kind: "flowchart", Options: DefaultOptions(), Boxes: []Box{{ID: "A", Exclusive: true}, {ID: "B", Exclusive: true}}, Routes: []Route{{ID: "e0", From: "A", To: "B", Orthogonal: true}}, Labels: []Label{{ID: "e0.label", Owner: "e0", Text: "yes", Lines: []string{"ignored"}}}}
	want := `{"version":1,"stage":"model","kind":"flowchart","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"TB","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},
"boxes":[{"id":"A","role":"node","parent":"","exclusive":true},
{"id":"B","role":"node","parent":"","exclusive":true}],
"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true}],
"labels":[{"id":"e0.label","owner":"e0","text":"yes","lines":[]}]}` + "\n"
	if got := string(d.AppendJSON(nil)); got != want {
		t.Fatalf("got %s; want %s", got, want)
	}
}

func TestDumpEscaping(t *testing.T) {
	d := Dump{Kind: "\"\\\b\t\n\f\r\x00\x1f/\x7fé", Options: DefaultOptions()}
	got := string(d.AppendJSON([]byte("prefix")))
	want := `"kind":"\"\\\b\t\n\f\r\u0000\u001f/` + "\x7fé" + `"`
	if !strings.Contains(got, want) || !strings.HasSuffix(got, "\n") || !strings.HasPrefix(got, "prefix") {
		t.Fatalf("invalid bytes: %q", got)
	}
}

func validDump() Dump {
	return Dump{Kind: "flowchart", Options: DefaultOptions(), Canvas: geom.Size{W: 100, H: 100}, Boxes: []Box{{ID: "A", Rect: geom.Rect{X: 0, Y: 0, W: 10, H: 10}, Exclusive: true}, {ID: "B", Rect: geom.Rect{X: 30, Y: 0, W: 10, H: 10}, Exclusive: true}}, Routes: []Route{{ID: "e", From: "A", To: "B", Orthogonal: true, Points: []geom.Point{{X: 10, Y: 5}, {X: 30, Y: 5}}}}}
}

func TestValidatorClauses(t *testing.T) {
	cases := []struct {
		name, message string
		change        func(*Dump)
	}{
		{"canvas", "box outside canvas", func(d *Dump) { d.Canvas.W = 35 }},
		{"exclusive-siblings", "exclusive sibling boxes overlap", func(d *Dump) { d.Boxes[1].Rect.X = 5 }},
		{"parent", "box outside its parent", func(d *Dump) { d.Boxes[1].Parent = "A" }},
		{"orthogonal", "orthogonal route has a diagonal segment", func(d *Dump) { d.Routes[0].Points[1].Y = 6 }},
		{"ports", "route end is off its box boundary", func(d *Dump) { d.Routes[0].Points[0].X = 11 }},
		{"route-clearance", "route crosses an exclusive box", func(d *Dump) {
			d.Boxes = append(d.Boxes, Box{ID: "C", Rect: geom.Rect{X: 15, Y: 0, W: 10, H: 10}, Exclusive: true})
		}},
		{"label-clearance", "label overlaps an exclusive box", func(d *Dump) { d.Labels = []Label{{ID: "l", Owner: "e", Rect: geom.Rect{X: 1, Y: 1, W: 2, H: 2}}} }},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			d := validDump()
			c.change(&d)
			cl, failed, err := d.Validate()
			if err != nil || !failed || cl.ID != c.name || cl.Message != c.message {
				t.Fatalf("%+v %v %v", cl, failed, err)
			}
		})
	}
	d := validDump()
	ok, err := d.Check()
	if !ok || err != nil {
		t.Fatalf("valid: %v %v", ok, err)
	}
	d.Canvas.W = 1
	d.Routes[0].Points = nil
	cl, _, err := d.Validate()
	if err != nil || cl.ID != "canvas" {
		t.Fatalf("order: %+v %v", cl, err)
	}
}

func TestLabelClearanceOwnBoxExempt(t *testing.T) {
	d := validDump()
	d.Labels = []Label{{ID: "l", Owner: "A", Rect: geom.Rect{X: 1, Y: 1, W: 2, H: 2}}}
	if clause, failed, err := d.Validate(); err != nil || failed {
		t.Fatalf("box-owned label inside its own exclusive box must pass: clause %+v failed %v err %v", clause, failed, err)
	}
}

func TestLabelClearanceOwnBoxForeignStillFails(t *testing.T) {
	d := validDump()
	d.Labels = []Label{{ID: "l", Owner: "A", Rect: geom.Rect{X: 31, Y: 1, W: 2, H: 2}}}
	clause, failed, err := d.Validate()
	if err != nil || !failed || clause != ClauseLabelClearance {
		t.Fatalf("box-owned label over a foreign exclusive box must fail: clause %+v failed %v err %v", clause, failed, err)
	}
}

func TestLabelClearanceRouteBoxCollisionPrefersRoute(t *testing.T) {
	d := validDump()
	d.Boxes = append(d.Boxes, Box{ID: "e", Rect: geom.Rect{X: 60, Y: 0, W: 10, H: 10}, Exclusive: true})
	d.Labels = []Label{{ID: "l", Owner: "e", Rect: geom.Rect{X: 61, Y: 1, W: 2, H: 2}}}
	clause, failed, err := d.Validate()
	if err != nil || !failed || clause != ClauseLabelClearance {
		t.Fatalf("colliding owner ID must keep route-first scope: clause %+v failed %v err %v", clause, failed, err)
	}
}

func TestWellFormed(t *testing.T) {
	changes := []func(*Dump){
		func(d *Dump) { d.Boxes[1].ID = "A" },
		func(d *Dump) { d.Boxes[1].Parent = "missing" },
		func(d *Dump) { d.Boxes[0].Parent = "B"; d.Boxes[1].Parent = "A" },
		func(d *Dump) { d.Boxes[0].Rect.X = int32(geom.CoordLimit) },
	}
	for i, change := range changes {
		d := validDump()
		change(&d)
		if err := d.WellFormed(); !errors.Is(err, ErrMalformed) {
			t.Fatalf("case %d: %v", i, err)
		}
	}
}

func TestLayoutGolden(t *testing.T) {
	d := validDump()
	want := `{"version":1,"stage":"layout","kind":"flowchart","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"TB","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},"canvas":{"w":100,"h":100},
"boxes":[{"id":"A","role":"node","x":0,"y":0,"w":10,"h":10,"parent":"","exclusive":true},
{"id":"B","role":"node","x":30,"y":0,"w":10,"h":10,"parent":"","exclusive":true}],
"routes":[{"id":"e","from":"A","to":"B","orthogonal":true,"points":[[10,5],[30,5]]}],
"labels":[]}` + "\n"
	if got := string(d.AppendJSON(nil)); got != want {
		t.Fatalf("got %s; want %s", got, want)
	}
}
