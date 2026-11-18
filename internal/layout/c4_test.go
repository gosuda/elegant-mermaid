package layout

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	model "github.com/gosuda/elegant-mermaid/internal/model/c4"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/c4"
)

func c4InputFromSource(t *testing.T, source string, profile scene.Profile) Input {
	t.Helper()
	ast, ds := parser.Parse([]byte(source), nil)
	if len(ds) != 0 {
		t.Fatalf("parse: %v", ds)
	}
	m, ds := model.Resolve([]byte(source), ast)
	if len(ds) != 0 {
		t.Fatalf("resolve: %v", ds)
	}
	in, ds := FromC4(m, profile, scene.Options{})
	if len(ds) != 0 {
		t.Fatalf("adapter: %v", ds)
	}
	return in
}

func TestC4AliasCollisionOwnership(t *testing.T) {
	in := c4InputFromSource(t, `C4Context
Person(c4group0, "Reserved")
Person(e0, "Route reservation")
Person(shared, "Element")
System_Boundary(shared, "Boundary") {
  System(child, "Child")
}
Rel(missing, child, "Omitted")
Rel(shared, child, "Kept")
`, scene.ProfileCell)
	boundary, childParent := c4BoundaryOwnership(in)
	if boundary != "c4group1" || childParent != boundary {
		t.Fatalf("boundary %q child parent %q", boundary, childParent)
	}
	c4AssertKeptRelation(t, in)
}

func c4BoundaryOwnership(in Input) (boundary, childParent string) {
	for _, b := range in.Boxes {
		if b.Role == scene.RoleGroup {
			boundary = b.ID
		}
		if b.ID == "child" {
			childParent = b.Parent
		}
	}
	return boundary, childParent
}

func c4AssertKeptRelation(t *testing.T, in Input) {
	t.Helper()
	if len(in.Routes) != 1 {
		t.Fatalf("routes: %v", in.Routes)
	}
	r := in.Routes[0]
	if r.ID != "e1" || r.From != "shared" || r.To != "child" {
		t.Fatalf("resolved relation: %+v", r)
	}
	for _, l := range in.Labels {
		if l.Text == "Kept" && l.Owner != r.ID {
			t.Fatalf("relation label owner %q", l.Owner)
		}
	}
}

func TestC4RelationIntent(t *testing.T) {
	for _, test := range []struct {
		macro, start, end string
		from, to          geom.Side
	}{
		{"Rel_Back", "point", "none", geom.SideNone, geom.SideNone},
		{"BiRel", "point", "point", geom.SideNone, geom.SideNone},
		{"Rel_Up", "none", "point", geom.SideTop, geom.SideBottom},
		{"Rel_Right", "none", "point", geom.SideRight, geom.SideLeft},
	} {
		t.Run(test.macro, func(t *testing.T) {
			in := c4InputFromSource(t, "C4Context\nSystem(a, \"A\")\nSystem(b, \"B\")\n"+test.macro+"(a, b, \"Link\")\n", scene.ProfileCell)
			r := in.Routes[0]
			if r.From != "a" || r.To != "b" || r.MarkerStart != test.start || r.MarkerEnd != test.end || r.FromSide != test.from || r.ToSide != test.to {
				t.Fatalf("relation intent: %+v", r)
			}
		})
	}
}

func TestC4OutlinesStayInsideMeasuredBoxes(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		in := c4InputFromSource(t, "C4Context\nPerson(p, \"Person\")\nSystemDb(db, \"Database\")\n", profile)
		s, _, err := layoutC4(in)
		if err != nil {
			t.Fatal(err)
		}
		for _, group := range s.Groups {
			if group.Role == scene.GroupRoleNode {
				c4AssertNodeOutline(t, s.Boxes, group, profile)
			}
		}
	}
}

const c4DirectionalSource = `C4Context
System(a, "A")
System(b, "B")
System(c, "C")
System(d, "D")
System(e, "E")
Rel(a, b, "Rel (default)")
Rel_U(a, c, "Rel_U")
Rel_D(a, d, "Rel_D")
Rel_L(a, e, "Rel_L")
Rel_R(b, c, "Rel_R")
`

func TestC4DirectionalRoutesStayDrawableInCells(t *testing.T) {
	in := c4InputFromSource(t, c4DirectionalSource, scene.ProfileCell)
	s, _, err := layoutC4(in)
	if err != nil {
		t.Fatal(err)
	}
	for _, r := range s.Routes {
		for i, p := range r.Points {
			if p.X < 0 || p.Y < 0 || p.X >= s.Canvas.W || p.Y >= s.Canvas.H {
				t.Fatalf("route %s point %d %+v is not a cell of canvas %+v", r.ID, i, p, s.Canvas)
			}
		}
	}
	if clause, failed, err := s.Validate(); err != nil || failed {
		t.Fatalf("validation: %v %v %v", clause.ID, clause.Message, err)
	}
}

type c4OutlineCounts struct {
	texts, ellipses, paths, symbols int
}

func c4AssertNodeOutline(t *testing.T, boxes []scene.Box, group *scene.Group, profile scene.Profile) {
	t.Helper()
	rect := c4OwnerRect(boxes, group.Owner)
	counts := c4AuditNodeOutline(t, rect, group.Items, profile)
	if counts.texts == 0 || counts.ellipses != 1 {
		t.Fatalf("%s: text %d ellipse %d", group.Owner, counts.texts, counts.ellipses)
	}
	if group.Owner != "db" {
		return
	}
	c4AssertCylinderProfile(t, profile, counts)
}

func c4OwnerRect(boxes []scene.Box, owner string) geom.Rect {
	var rect geom.Rect
	for _, b := range boxes {
		if b.ID == owner {
			rect = b.Rect
		}
	}
	return rect
}

func c4AuditNodeOutline(t *testing.T, rect geom.Rect, items []scene.Primitive, profile scene.Profile) c4OutlineCounts {
	t.Helper()
	var counts c4OutlineCounts
	for _, item := range items {
		switch p := item.(type) {
		case *scene.Text:
			counts.texts++
		case *scene.Ellipse:
			counts.ellipses++
			c4AssertEllipseInside(t, rect, p)
		case *scene.RoundRect:
			c4AssertRoundRectInside(t, rect, p)
		case *scene.Path:
			counts.paths++
			c4AssertPathInside(t, rect, p)
		case *scene.SymbolRef:
			counts.symbols++
			c4AssertDatabaseSymbol(t, p, profile)
		}
	}
	return counts
}

func c4AssertEllipseInside(t *testing.T, r geom.Rect, e *scene.Ellipse) {
	t.Helper()
	c4AssertPointInside(t, r, geom.Point{X: e.CX - e.RX, Y: e.CY - e.RY})
	c4AssertPointInside(t, r, geom.Point{X: e.CX + e.RX, Y: e.CY + e.RY})
}

func c4AssertRoundRectInside(t *testing.T, r geom.Rect, rr *scene.RoundRect) {
	t.Helper()
	c4AssertPointInside(t, r, geom.Point{X: rr.Rect.X, Y: rr.Rect.Y})
	c4AssertPointInside(t, r, geom.Point{X: rr.Rect.X + rr.Rect.W, Y: rr.Rect.Y + rr.Rect.H})
}

func c4AssertPathInside(t *testing.T, r geom.Rect, p *scene.Path) {
	t.Helper()
	for _, cmd := range p.Commands {
		c4AssertCommandInside(t, r, cmd)
	}
}

func c4AssertDatabaseSymbol(t *testing.T, p *scene.SymbolRef, profile scene.Profile) {
	t.Helper()
	if profile != scene.ProfileCell || p.Symbol != "database" {
		t.Fatalf("unexpected symbol: %+v", p)
	}
}

func c4AssertCylinderProfile(t *testing.T, profile scene.Profile, counts c4OutlineCounts) {
	t.Helper()
	wantPaths, wantSymbols := 1, 0
	label := "vector"
	if profile == scene.ProfileCell {
		wantPaths, wantSymbols = 0, 1
		label = "cell"
	}
	if counts.paths != wantPaths || counts.symbols != wantSymbols {
		t.Fatalf("%s cylinder: paths %d symbols %d", label, counts.paths, counts.symbols)
	}
}

func c4AssertPointInside(t *testing.T, r geom.Rect, p geom.Point) {
	t.Helper()
	if int64(p.X) < int64(r.X) || int64(p.X) > int64(r.X)+int64(r.W) || int64(p.Y) < int64(r.Y) || int64(p.Y) > int64(r.Y)+int64(r.H) {
		t.Fatalf("point %+v outside %+v", p, r)
	}
}

func c4AssertCommandInside(t *testing.T, r geom.Rect, cmd scene.Command) {
	t.Helper()
	switch p := cmd.(type) {
	case *scene.MoveTo:
		c4AssertPointInside(t, r, p.P)
	case *scene.LineTo:
		c4AssertPointInside(t, r, p.P)
	case *scene.CubicTo:
		c4AssertPointInside(t, r, p.C1)
		c4AssertPointInside(t, r, p.C2)
		c4AssertPointInside(t, r, p.P)
	case *scene.ClosePath:
	default:
		t.Fatalf("unexpected cylinder command %T", cmd)
	}
}
