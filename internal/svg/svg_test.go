package svg

import (
	"bytes"
	"encoding/xml"
	"errors"
	"io"
	"os"
	"regexp"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func sample() scene.Scene {
	return scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 12800, H: 3840}}, Groups: []*scene.Group{{Role: scene.GroupRoleEdge, Items: []scene.Primitive{&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Corner: 512, Points: []geom.Point{{X: 4480, Y: 1920}, {X: 8320, Y: 1920}}}, &scene.MarkerRef{Marker: "point", At: geom.Point{X: 8320, Y: 1920}}}}, {Role: scene.GroupRoleNode, Items: []scene.Primitive{&scene.Rect{Shape: scene.Shape{Style: "node"}, Rect: geom.Rect{X: 640, Y: 640, W: 3840, H: 2560}}, &scene.Text{Rect: geom.Rect{X: 640, Y: 640, W: 3840, H: 2560}, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: [][]scene.Run{{{Text: "A"}}}}}}, {Role: scene.GroupRoleNode, Items: []scene.Primitive{&scene.RoundRect{Shape: scene.Shape{Style: "node"}, Rect: geom.Rect{X: 8320, Y: 640, W: 3840, H: 2560}, R: 512}, &scene.Text{Rect: geom.Rect{X: 8320, Y: 640, W: 3840, H: 2560}, Role: scene.TextRoleLabel, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: [][]scene.Run{{{Text: "B"}}}}}}}}
}
func output(t *testing.T, s scene.Scene, o Options) string {
	t.Helper()
	var b bytes.Buffer
	if e := Write(&b, s, o); e != nil {
		t.Fatal(e)
	}
	d := xml.NewDecoder(strings.NewReader(b.String()))
	for {
		_, e := d.Token()
		if errors.Is(e, io.EOF) {
			break
		}
		if e != nil {
			t.Fatal(e)
		}
	}
	return b.String()
}
func TestGolden(t *testing.T) {
	want, e := os.ReadFile("testdata/two-box.svg")
	if e != nil {
		t.Fatal(e)
	}
	got := output(t, sample(), Options{Kind: "flowchart"})
	if got != string(want) {
		t.Fatalf("golden mismatch\n%s", got)
	}
}
func TestNumber(t *testing.T) {
	for _, c := range []struct {
		v int64
		s string
	}{{0, "0"}, {128, "2"}, {32, "0.5"}, {1, "0.02"}, {-96, "-1.5"}, {8, "0.13"}, {-8, "-0.13"}, {2147483647, "33554431.98"}} {
		if got := number(c.v); got != c.s {
			t.Errorf("%d: %s != %s", c.v, got, c.s)
		}
	}
}
func TestCorners(t *testing.T) {
	for _, c := range []struct {
		p    []geom.Point
		want string
	}{{[]geom.Point{{}, {X: 1280}, {X: 1280, Y: 1280}}, "M 0 0 L 12 0 A 8 8 0 0 1 20 8 L 20 20"}, {[]geom.Point{{}, {X: 384}, {X: 384, Y: 1280}}, "M 0 0 L 3 0 A 3 3 0 0 1 6 3 L 6 20"}, {[]geom.Point{{}, {X: 640}, {X: 1280}}, "M 0 0 L 10 0 L 20 0"}} {
		if got := rounded(c.p, 512); got != c.want {
			t.Errorf("%s != %s", got, c.want)
		}
	}
}
func TestMarkers(t *testing.T) {
	for axis, want := range []string{"10,10 2,14 2,6", "10,10 18,6 18,14", "10,10 6,2 14,2", "10,10 14,18 6,18"} {
		r := renderer{used: make(map[string]bool)}
		got, e := r.marker(&scene.MarkerRef{Marker: "point", At: geom.Point{X: 640, Y: 640}, Axis: scene.Axis(axis)})
		if e != nil || !strings.Contains(got, want) {
			t.Fatalf("%s %v", got, e)
		}
	}
}
func TestEscapingTheme(t *testing.T) {
	s := sample()
	opts := Options{Kind: "flowchart", Title: "<&\"' >\x01", Description: "a&b"}
	a := output(t, s, opts)
	if !strings.Contains(a, "&lt;&amp;&quot;&apos; &gt;�") {
		t.Fatal(a)
	}
	opts.Theme = "elegant-dark"
	b := output(t, s, opts)
	re := regexp.MustCompile(`#[0-9a-f]{6}`)
	if re.ReplaceAllString(a, "COLOUR") != re.ReplaceAllString(b, "COLOUR") {
		t.Fatal("theme changed structure")
	}
}
func TestPrimitivesStyles(t *testing.T) {
	s := sample()
	g := s.Groups[0]
	for _, style := range styleOrder {
		if strings.HasPrefix(style, "text") {
			continue
		}
		g.Items = append(g.Items, &scene.Ellipse{Shape: scene.Shape{Style: style, Line: scene.LineDotted}, CX: 640, CY: 640, RX: 64, RY: 64})
	}
	g.Items = append(g.Items, &scene.Polygon{Shape: scene.Shape{Style: "node"}, Points: []geom.Point{{}, {X: 64}, {Y: 64}}}, &scene.Path{Shape: scene.Shape{Style: "edge"}, Commands: []scene.Command{&scene.MoveTo{}, &scene.LineTo{P: geom.Point{X: 64}}, &scene.CubicTo{}, &scene.ArcTo{R: 64, Sweep: 16384}, &scene.ClosePath{}}})
	got := output(t, s, Options{})
	if strings.Contains(got, "foreignObject") {
		t.Fatal(got)
	}
}
func TestInvalidOptions(t *testing.T) {
	for _, o := range []Options{{Text: TextPaths}, {IDPrefix: "1bad"}, {Theme: "absent"}, {Background: "red"}} {
		if Write(io.Discard, sample(), o) == nil {
			t.Fatal(o)
		}
	}
	s := sample()
	s.Groups[0].Items = []scene.Primitive{&scene.SymbolRef{}}
	if Write(io.Discard, s, Options{}) == nil {
		t.Fatal("symbol accepted")
	}
}
