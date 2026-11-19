package svg

import (
	"bytes"
	"encoding/xml"
	"errors"
	"io"
	"regexp"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
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

type svgElementExpectation struct {
	name  string
	attrs map[string]string
	text  string
}

func TestTwoBoxSVG(t *testing.T) {
	want := []svgElementExpectation{
		{"svg", map[string]string{"viewBox": "0 0 200 60", "width": "200", "height": "60", "role": "graphics-document document", "aria-roledescription": "diagram", "aria-labelledby": "title"}, ""},
		{"title", map[string]string{"id": "title"}, "Mermaid flowchart diagram"},
		{"rect", map[string]string{"class": "emd-bg", "x": "0", "y": "0", "width": "200", "height": "60"}, ""},
		{"g", map[string]string{"class": "emd-edge", "id": "g0"}, ""},
		{"path", map[string]string{"class": "emd-s-edge", "d": "M 70 30 L 130 30", "stroke-width": "1"}, ""},
		{"polygon", map[string]string{"class": "emd-s-mark", "points": "130,30 122,34 122,26", "stroke-width": "1"}, ""},
		{"g", map[string]string{"class": "emd-node", "id": "g1"}, ""},
		{"rect", map[string]string{"class": "emd-s-node", "x": "10", "y": "10", "width": "60", "height": "40", "stroke-width": "1"}, ""},
		{"text", map[string]string{"x": "40", "font-size": "14", "text-anchor": "middle"}, ""},
		{"tspan", map[string]string{"x": "40", "y": "24.89"}, "A"},
		{"g", map[string]string{"class": "emd-node", "id": "g2"}, ""},
		{"rect", map[string]string{"class": "emd-s-node", "x": "130", "y": "10", "width": "60", "height": "40", "rx": "8", "ry": "8", "stroke-width": "1"}, ""},
		{"text", map[string]string{"x": "160", "font-size": "14", "text-anchor": "middle"}, ""},
		{"tspan", map[string]string{"x": "160", "y": "24.89"}, "B"},
	}
	assertSVGElements(t, output(t, sample(), Options{Kind: "flowchart"}), want)
}

func assertSVGElements(t *testing.T, document string, want []svgElementExpectation) {
	t.Helper()
	d := xml.NewDecoder(strings.NewReader(document))
	index := 0
	for {
		token, err := d.Token()
		if errors.Is(err, io.EOF) {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		start, ok := token.(xml.StartElement)
		if !ok {
			continue
		}
		if start.Name.Local == "style" {
			if err := d.Skip(); err != nil {
				t.Fatal(err)
			}
			continue
		}
		if index >= len(want) {
			t.Fatalf("unexpected element %s", start.Name.Local)
		}
		expected := want[index]
		index++
		assertSVGElement(t, d, start, expected, index)
	}
	if index != len(want) {
		t.Errorf("got %d elements, want %d", index, len(want))
	}
}

func assertSVGElement(t *testing.T, d *xml.Decoder, start xml.StartElement, expected svgElementExpectation, index int) {
	t.Helper()
	if start.Name.Local != expected.name {
		t.Fatalf("element %d = %s, want %s", index, start.Name.Local, expected.name)
	}
	attrs := svgAttributes(start)
	for name, value := range expected.attrs {
		if attrs[name] != value {
			t.Errorf("%s %s = %q, want %q", expected.name, name, attrs[name], value)
		}
	}
	if expected.text == "" {
		return
	}
	var text string
	if err := d.DecodeElement(&text, &start); err != nil {
		t.Fatal(err)
	}
	if text != expected.text {
		t.Errorf("%s text = %q, want %q", expected.name, text, expected.text)
	}
}

func svgAttributes(start xml.StartElement) map[string]string {
	attrs := make(map[string]string)
	for _, attr := range start.Attr {
		attrs[attr.Name.Local] = attr.Value
	}
	return attrs
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
		got, e := r.marker(&scene.MarkerRef{Marker: "point", At: geom.Point{X: 640, Y: 640}, Axis: scene.Axis(axis)}, 0)
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
	for _, row := range gen.Styles {
		style := row.Name
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

func TestRoundStrokePresentation(t *testing.T) {
	s := sample()
	s.Groups[0].Items = append(s.Groups[0].Items,
		&scene.Rect{Shape: scene.Shape{Style: "ink"}, Rect: geom.Rect{W: 64, H: 64}},
		&scene.Polyline{Shape: scene.Shape{Style: "rule"}, Points: []geom.Point{{}, {X: 64}, {X: 64, Y: 64}}},
	)
	stylesheet, openClasses := svgStrokeStyles(t, output(t, s, Options{}))
	rules := parseSVGStyleRules(stylesheet)
	assertRoundOpenStrokes(t, rules, openClasses)
	assertFillOnlyStyles(t, rules)
}

func svgStrokeStyles(t *testing.T, document string) (string, []string) {
	t.Helper()
	d := xml.NewDecoder(strings.NewReader(document))
	var stylesheet string
	var openClasses []string
	for {
		token, err := d.Token()
		if errors.Is(err, io.EOF) {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		start, ok := token.(xml.StartElement)
		if !ok {
			continue
		}
		if start.Name.Local == "style" {
			if err := d.DecodeElement(&stylesheet, &start); err != nil {
				t.Fatal(err)
			}
		}
		if start.Name.Local == "polyline" || start.Name.Local == "path" {
			openClasses = append(openClasses, strings.Fields(svgAttributes(start)["class"])...)
		}
	}
	return stylesheet, openClasses
}

func parseSVGStyleRules(stylesheet string) map[string]map[string]string {
	rules := make(map[string]map[string]string)
	for rule := range strings.SplitSeq(stylesheet, "}") {
		selector, body, ok := strings.Cut(rule, "{")
		if !ok {
			continue
		}
		rules[strings.TrimPrefix(strings.TrimSpace(selector), ".")] = parseSVGStyleProperties(body)
	}
	return rules
}

func parseSVGStyleProperties(body string) map[string]string {
	properties := make(map[string]string)
	for declaration := range strings.SplitSeq(body, ";") {
		name, value, ok := strings.Cut(declaration, ":")
		if ok {
			properties[strings.TrimSpace(name)] = strings.TrimSpace(value)
		}
	}
	return properties
}

func assertRoundOpenStrokes(t *testing.T, rules map[string]map[string]string, openClasses []string) {
	t.Helper()
	if len(openClasses) == 0 {
		t.Fatal("no open strokes emitted")
	}
	for _, class := range openClasses {
		for _, property := range []string{"stroke-linecap", "stroke-linejoin"} {
			if rules[class][property] != "round" {
				t.Errorf("%s %s = %q, want round", class, property, rules[class][property])
			}
		}
	}
}

func assertFillOnlyStyles(t *testing.T, rules map[string]map[string]string) {
	t.Helper()
	for _, class := range []string{"emd-s-ink", "emd-s-text"} {
		if rules[class]["fill"] == "" {
			t.Fatalf("missing fill-only class %s", class)
		}
		for _, property := range []string{"stroke-linecap", "stroke-linejoin"} {
			if _, ok := rules[class][property]; ok {
				t.Errorf("fill-only class %s sets %s", class, property)
			}
		}
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
