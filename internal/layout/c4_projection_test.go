package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestC4CellAttachmentProjection(t *testing.T) {
	for _, test := range []struct {
		name  string
		macro string
		side  geom.Side
	}{
		{"Rel_Up arrow on painted bottom row", "Rel_Up", geom.SideBottom},
		{"Rel_Left arrow on painted right column", "Rel_Left", geom.SideRight},
	} {
		t.Run(test.name, func(t *testing.T) {
			in := c4InputFromSource(t, "C4Context\nPerson(a, \"A\")\nSystemDb(b, \"B\")\n"+test.macro+"(a, b, \"Uses\")\n", scene.ProfileCell)
			s, ds, err := Layout(in)
			if err != nil {
				t.Fatal(err)
			}
			if len(ds) != 0 {
				t.Fatalf("diagnostics: %v", ds)
			}
			c4AssertPaintedTargetAttachment(t, s, test.side)
		})
	}
}

func c4AssertPaintedTargetAttachment(t *testing.T, s scene.Scene, side geom.Side) {
	t.Helper()
	route := c4TargetRoute(t, s)
	rect, ok := c4BoxRect(s, "b")
	if !ok {
		t.Fatalf("box b: %+v", s.Boxes)
	}
	if route.MarkerStart != "" || route.MarkerEnd == "" {
		t.Fatalf("single end marker expected: %+v", route)
	}
	if len(route.Points) < 2 {
		t.Fatalf("route points: %+v", route)
	}
	raw := route.Points[len(route.Points)-1]
	port, ok := c4SidePort(side, rect)
	if !ok || raw != port {
		t.Fatalf("dump route end %v off the raw %v face of rect %+v", raw, side, rect)
	}
	painted := c4PaintedPoint(rect, raw)
	marker, line := c4EdgeEnds(t, s, route.ID)
	if marker.At != painted {
		t.Fatalf("arrowhead off painted border: at %v want %v (rect %+v, dump end %v)", marker.At, painted, rect, raw)
	}
	c4AssertPaintedLine(t, line, painted)
}

func c4TargetRoute(t *testing.T, s scene.Scene) *scene.Route {
	t.Helper()
	for i := range s.Routes {
		if s.Routes[i].To == "b" {
			return &s.Routes[i]
		}
	}
	t.Fatalf("route into b: %+v", s.Routes)
	return nil
}

func c4BoxRect(s scene.Scene, id string) (geom.Rect, bool) {
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect, true
		}
	}
	return geom.Rect{}, false
}

func c4EdgeEnds(t *testing.T, s scene.Scene, owner string) (*scene.MarkerRef, *scene.Polyline) {
	t.Helper()
	group := c4EdgeGroup(t, s, owner)
	var marker *scene.MarkerRef
	var line *scene.Polyline
	for _, item := range group.Items {
		switch v := item.(type) {
		case *scene.MarkerRef:
			if marker != nil {
				t.Fatalf("one end marker expected, got %+v and %+v", marker, v)
			}
			marker = v
		case *scene.Polyline:
			line = v
		}
	}
	if marker == nil {
		t.Fatalf("end marker missing in group %s", owner)
	}
	return marker, line
}

func c4AssertPaintedLine(t *testing.T, line *scene.Polyline, painted geom.Point) {
	t.Helper()
	if line == nil {
		return
	}
	if len(line.Points) < 2 || line.Points[len(line.Points)-1] != painted {
		t.Fatalf("drawn line off painted border: end %v want %v", line.Points[len(line.Points)-1], painted)
	}
}

func c4SidePort(side geom.Side, rect geom.Rect) (geom.Point, bool) {
	x, y := rect.X+rect.W/2, rect.Y+rect.H/2
	switch side {
	case geom.SideLeft:
		return geom.Point{X: rect.X, Y: y}, true
	case geom.SideRight:
		return geom.Point{X: rect.X + rect.W, Y: y}, true
	case geom.SideTop:
		return geom.Point{X: x, Y: rect.Y}, true
	case geom.SideBottom:
		return geom.Point{X: x, Y: rect.Y + rect.H}, true
	}
	return geom.Point{}, false
}

func c4PaintedPoint(rect geom.Rect, p geom.Point) geom.Point {
	painted := p
	if p.Y == rect.Y+rect.H {
		painted.Y = rect.Y + rect.H - 1
	}
	if p.X == rect.X+rect.W {
		painted.X = rect.X + rect.W - 1
	}
	return painted
}

func c4EdgeGroup(t *testing.T, s scene.Scene, owner string) *scene.Group {
	t.Helper()
	for _, g := range s.Groups {
		if g.Role == scene.GroupRoleEdge && g.Owner == owner {
			return g
		}
	}
	t.Fatalf("edge group %s missing", owner)
	return nil
}
