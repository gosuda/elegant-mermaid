package icon

import (
	"errors"
	"fmt"
	"reflect"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func commandsText(cs []scene.Command) string {
	var parts []string
	for _, c := range cs {
		switch v := c.(type) {
		case *scene.MoveTo:
			parts = append(parts, fmt.Sprintf("M%d,%d", v.P.X, v.P.Y))
		case *scene.LineTo:
			parts = append(parts, fmt.Sprintf("L%d,%d", v.P.X, v.P.Y))
		case *scene.CubicTo:
			parts = append(parts, fmt.Sprintf("C%d,%d,%d,%d,%d,%d", v.C1.X, v.C1.Y, v.C2.X, v.C2.Y, v.P.X, v.P.Y))
		case *scene.ClosePath:
			parts = append(parts, "Z")
		}
	}
	return strings.Join(parts, " ")
}

func mustPack(t *testing.T, data string) *Pack {
	t.Helper()
	p, err := Parse([]byte(data))
	if err != nil {
		t.Fatal(err)
	}
	return p
}

func TestParsePathCommands(t *testing.T) {
	for _, c := range []struct {
		d, want string
	}{
		{"M1 2L3 4Z", "M1 2 L3 4 Z"},
		{"m1,2 3,4 h5 v-1z", "M1 2 L4 6 L9 6 L9 5 Z"},
		{"M0 0C1 1 2 2 3 3S5 5 6 6", "M0 0 C1 1 2 2 3 3 C4 4 5 5 6 6"},
		{"M0 0Q1 2 3 0T6 0", "M0 0 Q1 2 3 0 Q5 -2 6 0"},
		{"M.5-.5l.25.25", "M0.5 -0.5 L0.75 -0.25"},
		{"M1 1h1 1", "M1 1 L2 1 L3 1"},
	} {
		cmds, ok := parsePath(c.d)
		if !ok {
			t.Fatalf("%q rejected", c.d)
		}
		var got []string
		for _, cmd := range cmds {
			got = append(got, describe(cmd))
		}
		if strings.Join(got, " ") != c.want {
			t.Errorf("%q = %q, want %q", c.d, strings.Join(got, " "), c.want)
		}
	}
}

func describe(c command) string {
	if c.op == 'Z' {
		return "Z"
	}
	n := map[byte]int{'M': 1, 'L': 1, 'C': 3, 'Q': 2}[c.op]
	var parts []string
	for _, p := range c.p[:n] {
		parts = append(parts, fixedText(p.x)+" "+fixedText(p.y))
	}
	return string(c.op) + strings.Join(parts, " ")
}

func fixedText(v int64) string {
	sign := ""
	if v < 0 {
		sign, v = "-", -v
	}
	s := fmt.Sprintf("%d.%06d", v/fixedScale, v%fixedScale)
	return sign + strings.TrimRight(strings.TrimRight(s, "0"), ".")
}

func TestParsePathRejects(t *testing.T) {
	for _, d := range []string{"", "L1 1", "M0 0A1 1 0 0 1 2 2", "M0 0 1", "M0 0Z1 1", "M1e3 0", "M0", "M0 0 x", "M1000000 0", "M0 0L-"} {
		if _, ok := parsePath(d); ok {
			t.Errorf("%q accepted", d)
		}
	}
}

func TestParsePackRejects(t *testing.T) {
	for _, data := range []string{
		"", "[]", "{}", `{"prefix":"x"}`, `{"icons":{}}`, `{"prefix":"","icons":{}}`,
		`{"prefix":"x","icons":{"a":{}}}`, `{"prefix":"x","icons":{"a":{"body":"","width":"wide"}}}`,
		`{"prefix":"x","icons":{}} trailing`, "{\"prefix\":\"x\",\"icons\":{\"a\":{\"body\":\"\xff\"}}}",
		`{"prefix":"x","icons":{"a":{"body":1}}}`,
	} {
		_, err := Parse([]byte(data))
		if _, ok := errors.AsType[*FormatError](err); !ok {
			t.Errorf("%q: %v", data, err)
		}
	}
}

func TestDrawPackIcon(t *testing.T) {
	p := mustPack(t, `{"prefix":"p","icons":{"sq":{"body":"<path fill=\"currentColor\" d=\"M0 0h24v24H0z\"/>","width":24,"height":24},"ofs":{"body":"<path d='M2 2h4v4z'/>","width":8,"height":4,"left":2,"top":2}}}`)
	got := Draw([]*Pack{p}, "p:sq", geom.Point{X: 100, Y: 200}, scene.ProfileVector)
	if got.Missing || len(got.Items) != 1 {
		t.Fatalf("%+v", got)
	}
	path, ok := got.Items[0].(*scene.Path)
	if !ok || path.Style != "ink" {
		t.Fatalf("%#v", got.Items[0])
	}
	if want := "M100,200 L1636,200 L1636,1736 L100,1736 Z"; commandsText(path.Commands) != want {
		t.Errorf("%s != %s", commandsText(path.Commands), want)
	}
	got = Draw([]*Pack{p}, "p:ofs", geom.Point{}, scene.ProfileVector)
	path = got.Items[0].(*scene.Path)
	if want := "M0,384 L768,384 L768,1152 Z"; commandsText(path.Commands) != want {
		t.Errorf("%s != %s", commandsText(path.Commands), want)
	}
}

func TestDrawPackScaleRoundsHalfUp(t *testing.T) {
	p := mustPack(t, `{"prefix":"p","icons":{"a":{"body":"<path d=\"M0 0h20v20z\"/>","width":20,"height":20}}}`)
	path := Draw([]*Pack{p}, "p:a", geom.Point{}, scene.ProfileVector).Items[0].(*scene.Path)
	if want := "M-2,-2 L1538,-2 L1538,1538 Z"; commandsText(path.Commands) != want {
		t.Errorf("%s != %s", commandsText(path.Commands), want)
	}
}

func TestPackRootDefaults(t *testing.T) {
	p := mustPack(t, `{"prefix":"p","width":24,"height":24,"icons":{"a":{"body":"<path d=\"M0 0h24v24z\"/>"}}}`)
	path := Draw([]*Pack{p}, "p:a", geom.Point{}, scene.ProfileVector).Items[0].(*scene.Path)
	if want := "M0,0 L1536,0 L1536,1536 Z"; commandsText(path.Commands) != want {
		t.Errorf("%s != %s", commandsText(path.Commands), want)
	}
}

func TestUnsupportedBodiesDrawUnknown(t *testing.T) {
	bodies := []string{
		`<g><path d='M0 0h1v1z'/></g>`, `<rect width='1' height='1'/>`, `<path d='M0 0A1 1 0 0 1 2 2'/>`,
		`<path d='M0 0h1v1z' fill='red'/>`, `<path d='M0 0h1v1z' stroke='red'/>`, `<path fill='currentColor'/>`,
		`<path d='M0 0h1v1z'/> text`, `<pathd='M0 0'/>`,
	}
	for _, body := range bodies {
		data := fmt.Sprintf(`{"prefix":"p","icons":{"a":{"body":%q}}}`, body)
		got := Draw([]*Pack{mustPack(t, data)}, "p:a", geom.Point{}, scene.ProfileVector)
		if !got.Missing {
			t.Errorf("%s drawn", body)
		}
		if path, ok := got.Items[0].(*scene.Path); !ok || path.Style != "ink" || len(path.Commands) < 10 {
			t.Errorf("%s: fallback %#v", body, got.Items[0])
		}
	}
}

func assertMissingDrawsUnknown(t *testing.T, p *Pack, name string) {
	t.Helper()
	got := Draw([]*Pack{p}, name, geom.Point{X: 64, Y: 64}, scene.ProfileVector)
	if !got.Missing || len(got.Items) != 1 {
		t.Errorf("%q: %+v", name, got)
	}
	cell := Draw([]*Pack{p}, name, geom.Point{X: 3, Y: 4}, scene.ProfileCell)
	sym, ok := cell.Items[0].(*scene.SymbolRef)
	if !cell.Missing || !ok || sym.Symbol != "unknown" || sym.Style != "ink" || sym.At != (geom.Point{X: 3, Y: 4}) {
		t.Errorf("%q cell: %+v", name, cell)
	}
}

func TestMissingIcons(t *testing.T) {
	p := mustPack(t, `{"prefix":"p","icons":{"a":{"body":""}}}`)
	for _, name := range []string{"p:b", "q:a", "nothing", "a", ""} {
		assertMissingDrawsUnknown(t, p, name)
	}
	if got := Draw([]*Pack{p}, "p:a", geom.Point{}, scene.ProfileVector); got.Missing || len(got.Items) != 0 {
		t.Errorf("blank icon: %+v", got)
	}
}

func TestMissingDiagnostic(t *testing.T) {
	d := MissingDiagnostic("p:b", source.Span{Start: 3, End: 5})
	if d.Code != "icon/pack-missing" || d.Severity.String() != "info" || d.Message != "icon p:b is not available" || d.Span != (source.Span{Start: 3, End: 5}) || d.Help == "" {
		t.Errorf("%+v", d)
	}
}

func TestBuiltinIcons(t *testing.T) {
	for _, name := range builtinNames() {
		got := Draw(nil, name, geom.Point{X: 640, Y: 640}, scene.ProfileVector)
		if got.Missing || len(got.Items) == 0 {
			t.Fatalf("%s: %+v", name, got)
		}
		for _, c := range got.Items {
			assertInsideBox(t, name, c, geom.Rect{X: 640, Y: 640, W: boxUnits, H: boxUnits})
		}
		cell := Draw(nil, name, geom.Point{X: 1, Y: 2}, scene.ProfileCell)
		sym := cell.Items[0].(*scene.SymbolRef)
		wantStyle := "ink-line"
		if name == "unknown" {
			wantStyle = "ink"
		}
		if cell.Missing || sym.Symbol != name || sym.Style != wantStyle {
			t.Errorf("%s cell: %+v %+v", name, cell, sym)
		}
	}
}

func assertInsideBox(t *testing.T, name string, p scene.Primitive, box geom.Rect) {
	t.Helper()
	var points []geom.Point
	switch v := p.(type) {
	case *scene.RoundRect:
		points = []geom.Point{{X: v.Rect.X, Y: v.Rect.Y}, {X: v.Rect.X + v.Rect.W, Y: v.Rect.Y + v.Rect.H}}
	case *scene.Ellipse:
		points = []geom.Point{{X: v.CX - v.RX, Y: v.CY - v.RY}, {X: v.CX + v.RX, Y: v.CY + v.RY}}
	case *scene.Polyline:
		points = v.Points
	case *scene.Path:
		points = pathPoints(v.Commands)
	default:
		t.Fatalf("%s: unexpected %T", name, p)
	}
	for _, q := range points {
		if q.X < box.X || q.Y < box.Y || q.X > box.X+box.W || q.Y > box.Y+box.H {
			t.Errorf("%s: point %v outside %v", name, q, box)
		}
	}
}

func pathPoints(cs []scene.Command) []geom.Point {
	var out []geom.Point
	for _, c := range cs {
		switch v := c.(type) {
		case *scene.MoveTo:
			out = append(out, v.P)
		case *scene.LineTo:
			out = append(out, v.P)
		case *scene.CubicTo:
			out = append(out, v.C1, v.C2, v.P)
		}
	}
	return out
}

func TestBuiltinIconsAreDeterministic(t *testing.T) {
	for _, name := range builtinNames() {
		a := Draw(nil, name, geom.Point{}, scene.ProfileVector)
		b := Draw(nil, name, geom.Point{}, scene.ProfileVector)
		if !reflect.DeepEqual(a, b) {
			t.Errorf("%s differs between draws", name)
		}
	}
}
