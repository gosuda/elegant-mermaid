package railroad

import (
	"errors"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var cellConstants = Constants{
	PadX: 1, PadY: 1, LineHeight: 1, Hsep: 2, Vsep: 1,
	ArcRadius: 1, TerminalRadius: 0, MarkerRadius: 1, Margin: 1,
	RuleNameGap: 2, RuleEndGap: 2, RuleMinBaseline: 2,
	RuleMinHeight: 3, EmptyWidth: 20, EmptyHeight: 5,
}

func cellParams() Params {
	return Params{Profile: scene.ProfileCell, Options: scene.DefaultOptions(), Constants: cellConstants, Metric: measure.CellMetric()}
}

func leaf(id, text string) *Node { return &Node{ID: id, Kind: KindTerminal, Text: text} }

func composite(id string, kind Kind, children ...*Node) *Node {
	return &Node{ID: id, Kind: kind, Children: children}
}

func layoutOne(t *testing.T, root *Node) scene.Scene {
	t.Helper()
	s, err := Layout([]Rule{{ID: "r0", Title: "r =", Root: root}}, cellParams())
	if err != nil {
		t.Fatal(err)
	}
	return s
}

func boxRect(t *testing.T, s scene.Scene, id string) geom.Rect {
	t.Helper()
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect
		}
	}
	t.Fatalf("no box %s", id)
	return geom.Rect{}
}

func wantRect(t *testing.T, s scene.Scene, id string, want geom.Rect) {
	t.Helper()
	if got := boxRect(t, s, id); got != want {
		t.Fatalf("box %s: got %v want %v", id, got, want)
	}
}

func TestSingleTerminalRule(t *testing.T) {
	s := layoutOne(t, leaf("r0.0", "ab"))
	wantRect(t, s, "r0", geom.Rect{X: 0, Y: 1, W: 16, H: 6})
	wantRect(t, s, "r0.0", geom.Rect{X: 8, Y: 2, W: 4, H: 3})
	if s.Canvas != (geom.Size{W: 16, H: 9}) {
		t.Fatalf("canvas %v", s.Canvas)
	}
	if len(s.Labels) != 1 || s.Labels[0].ID != "r0.label" || s.Labels[0].Rect != (geom.Rect{X: 1, Y: 3, W: 3, H: 1}) {
		t.Fatalf("labels %+v", s.Labels)
	}
}

func TestSequenceJoinsAlignCentreLines(t *testing.T) {
	tall := composite("r0.2", KindChoice, leaf("r0.3", "x"), leaf("r0.4", "y"))
	s := layoutOne(t, composite("r0.0", KindSequence, leaf("r0.1", "a"), tall))
	wantRect(t, s, "r0.0", geom.Rect{X: 8, Y: 1, W: 3 + 2 + 7, H: 7})
	wantRect(t, s, "r0.1", geom.Rect{X: 8, Y: 3, W: 3, H: 3})
	wantRect(t, s, "r0.2", geom.Rect{X: 13, Y: 1, W: 7, H: 7})
	if len(s.Routes) != 1 || s.Routes[0].ID != "e0" || s.Routes[0].From != "r0.1" || s.Routes[0].To != "r0.2" {
		t.Fatalf("routes %+v", s.Routes)
	}
	want := []geom.Point{{X: 11, Y: 4}, {X: 13, Y: 4}}
	if got := s.Routes[0].Points; len(got) != 2 || got[0] != want[0] || got[1] != want[1] {
		t.Fatalf("points %v", got)
	}
}

func TestChoiceCentresNarrowAlternatives(t *testing.T) {
	s := layoutOne(t, composite("r0.0", KindChoice, leaf("r0.1", "abcd"), leaf("r0.2", "a")))
	wantRect(t, s, "r0.0", geom.Rect{X: 8, Y: 1, W: 6 + 4, H: 7})
	wantRect(t, s, "r0.1", geom.Rect{X: 10, Y: 1, W: 6, H: 3})
	wantRect(t, s, "r0.2", geom.Rect{X: 11, Y: 5, W: 3, H: 3})
}

func TestOptionalAndRepetitionBands(t *testing.T) {
	cases := []struct {
		kind       Kind
		w, h, y, x int32
	}{
		{KindOptional, 3 + 4, 3 + 2, 2, 2},
		{KindZeroOrMore, 3 + 4, 3 + 4, 2, 2},
		{KindOneOrMore, 3 + 4, 3 + 2, 0, 2},
	}
	for _, c := range cases {
		s := layoutOne(t, composite("r0.0", c.kind, leaf("r0.1", "a")))
		outer := boxRect(t, s, "r0.0")
		if outer.W != c.w || outer.H != c.h {
			t.Fatalf("kind %d: outer %v", c.kind, outer)
		}
		wantRect(t, s, "r0.1", geom.Rect{X: outer.X + c.x, Y: outer.Y + c.y, W: 3, H: 3})
	}
}

func TestRuleBoxesStackWithVerticalSeparation(t *testing.T) {
	rules := []Rule{
		{ID: "r0", Title: "a =", Root: leaf("r0.0", "x")},
		{ID: "r1", Title: "b =", Root: leaf("r1.0", "y")},
	}
	s, err := Layout(rules, cellParams())
	if err != nil {
		t.Fatal(err)
	}
	first, second := boxRect(t, s, "r0"), boxRect(t, s, "r1")
	if second.Y != first.Y+first.H+1 {
		t.Fatalf("rules at %v and %v", first, second)
	}
	if s.Canvas.H != second.Y+second.H+1+1 {
		t.Fatalf("canvas %v", s.Canvas)
	}
}

func TestEmptyDocumentCanvas(t *testing.T) {
	s, err := Layout(nil, cellParams())
	if err != nil {
		t.Fatal(err)
	}
	if s.Canvas != (geom.Size{W: 20, H: 5}) || len(s.Boxes) != 0 {
		t.Fatalf("%v %d", s.Canvas, len(s.Boxes))
	}
}

func TestArityViolations(t *testing.T) {
	for _, root := range []*Node{
		composite("r0.0", KindChoice, leaf("r0.1", "a")),
		composite("r0.0", KindSequence),
		composite("r0.0", KindOptional, leaf("r0.1", "a"), leaf("r0.2", "b")),
		{ID: "r0.0", Kind: KindTerminal, Children: []*Node{leaf("r0.1", "a")}},
		nil,
	} {
		_, err := Layout([]Rule{{ID: "r0", Root: root}}, cellParams())
		if !errors.Is(err, ErrArity) {
			t.Fatalf("got %v", err)
		}
	}
}

func TestOverflowIsReported(t *testing.T) {
	p := cellParams()
	p.Constants.PadX = int64(geom.I32Max)
	if _, err := Layout([]Rule{{ID: "r0", Root: leaf("r0.0", "a")}}, p); !errors.Is(err, geom.ErrOverflow) {
		t.Fatalf("got %v", err)
	}
}

func TestJoinsFollowPreorder(t *testing.T) {
	inner := composite("r0.2", KindSequence, leaf("r0.3", "b"), leaf("r0.4", "c"))
	outer := composite("r0.0", KindSequence, leaf("r0.1", "a"), inner, leaf("r0.5", "d"))
	got := Joins([]Rule{{ID: "r0", Root: outer}})
	want := []Join{{"e0", "r0.1", "r0.2"}, {"e1", "r0.2", "r0.5"}, {"e2", "r0.3", "r0.4"}}
	if len(got) != len(want) {
		t.Fatalf("%v", got)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatalf("join %d: %v want %v", i, got[i], want[i])
		}
	}
	s := layoutOne(t, outer)
	for i, route := range s.Routes {
		if route.ID != want[i].ID || route.From != want[i].From || route.To != want[i].To {
			t.Fatalf("route %d: %+v", i, route)
		}
	}
}

func arcsOf(t *testing.T, s scene.Scene, owner string) []*scene.ArcTo {
	t.Helper()
	var arcs []*scene.ArcTo
	for _, g := range s.Groups {
		if g.Owner == owner {
			arcs = append(arcs, groupArcs(t, g)...)
		}
	}
	return arcs
}

func groupArcs(t *testing.T, g *scene.Group) []*scene.ArcTo {
	t.Helper()
	var arcs []*scene.ArcTo
	for _, item := range g.Items {
		path, ok := item.(*scene.Path)
		if !ok {
			t.Fatalf("rail is %T", item)
		}
		for _, command := range path.Commands {
			if arc, ok := command.(*scene.ArcTo); ok {
				arcs = append(arcs, arc)
			}
		}
	}
	return arcs
}

func TestVectorLoopUsesQuarterArcs(t *testing.T) {
	p := cellParams()
	p.Profile = scene.ProfileVector
	p.Metric = measure.ForRole(measure.RoleLabel)
	p.Constants = Constants{
		PadX: 640, PadY: 640, LineHeight: 1280, Hsep: 640, Vsep: 512,
		ArcRadius: 640, TerminalRadius: 640, MarkerRadius: 320, Margin: 640,
		RuleNameGap: 1280, RuleEndGap: 640, RuleMinBaseline: 1280,
		RuleMinHeight: 2560, EmptyWidth: 12800, EmptyHeight: 6400,
	}
	s, err := Layout([]Rule{{ID: "r0", Title: "r =", Root: composite("r0.0", KindOneOrMore, leaf("r0.1", "a"))}}, p)
	if err != nil {
		t.Fatal(err)
	}
	arcs := arcsOf(t, s, "r0.0")
	if len(arcs) != 4 {
		t.Fatalf("%d arcs", len(arcs))
	}
	for _, arc := range arcs {
		if arc.R != 640 || arc.Sweep != 16384 && arc.Sweep != -16384 {
			t.Fatalf("arc %+v", arc)
		}
	}
}
