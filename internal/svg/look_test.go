package svg

import (
	"bytes"
	"encoding/xml"
	"errors"
	"fmt"
	"io"
	"regexp"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var cssRule = regexp.MustCompile(`\.([a-zA-Z0-9_-]+)\{([^}]*)\}`)

type paintedElement struct {
	name  string
	attrs map[string]string
	paint map[string]string
}

func drawingStyleRules(output string) map[string]map[string]string {
	rules := map[string]map[string]string{}
	for _, match := range cssRule.FindAllStringSubmatch(output, -1) {
		properties := map[string]string{}
		for declaration := range strings.SplitSeq(match[2], ";") {
			key, value, ok := strings.Cut(declaration, ":")
			if ok {
				properties[key] = value
			}
		}
		rules[match[1]] = properties
	}
	return rules
}

func drawingElements(t *testing.T, output string) []paintedElement {
	t.Helper()
	rules := drawingStyleRules(output)
	decoder := xml.NewDecoder(strings.NewReader(output))
	var elements []paintedElement
	for {
		token, err := decoder.Token()
		if errors.Is(err, io.EOF) {
			return elements
		}
		if err != nil {
			t.Fatal(err)
		}
		start, ok := token.(xml.StartElement)
		if !ok {
			continue
		}
		switch start.Name.Local {
		case "rect", "path", "polyline", "polygon", "ellipse":
		default:
			continue
		}
		element := paintedDrawingElement(start, rules)
		elements = append(elements, element)
	}
}

func paintedDrawingElement(start xml.StartElement, rules map[string]map[string]string) paintedElement {
	element := paintedElement{name: start.Name.Local, attrs: map[string]string{}, paint: map[string]string{}}
	for _, attr := range start.Attr {
		element.attrs[attr.Name.Local] = attr.Value
	}
	for class := range strings.FieldsSeq(element.attrs["class"]) {
		for key, value := range rules[class] {
			element.paint[key] = value
		}
	}
	return element
}

func quadraticStrokes(t *testing.T, output string) []paintedElement {
	t.Helper()
	var strokes []paintedElement
	for _, element := range drawingElements(t, output) {
		if element.name == "path" && strings.Contains(element.attrs["d"], " Q ") {
			if element.paint["fill"] != "none" || element.paint["stroke"] == "" || element.paint["stroke"] == "none" {
				t.Fatalf("sketched stroke must have stroke paint and no fill: %+v", element)
			}
			strokes = append(strokes, element)
		}
	}
	return strokes
}

func sketchOutput(t *testing.T, s scene.Scene, look scene.Look) string {
	t.Helper()
	return output(t, s, Options{Kind: "flowchart", Look: look})
}

func TestLookHandDrawnSeed(t *testing.T) {
	hand := scene.Look{Kind: scene.LookHandDrawn, Seed: 7}
	a, b := sketchOutput(t, sample(), hand), sketchOutput(t, sample(), hand)
	if a != b {
		t.Fatal("two renders with seed 7 differ")
	}
	if plain := sketchOutput(t, sample(), scene.Look{}); a == plain {
		t.Fatal("handDrawn output equals classic output")
	}
	if other := sketchOutput(t, sample(), scene.Look{Kind: scene.LookHandDrawn, Seed: 8}); a == other {
		t.Fatal("seeds 7 and 8 render the same")
	}
	zero := scene.Look{Kind: scene.LookHandDrawn}
	first, second := sketchOutput(t, sample(), zero), sketchOutput(t, sample(), zero)
	if first != second {
		t.Fatal("two renders with seed 0 differ")
	}
}

func TestSketchSeedRule(t *testing.T) {
	if got := newSketcher(sketchMultiplier, 0).state; got != 1 {
		t.Errorf("zero state = %d, want 1", got)
	}
	if got := newSketcher(0, 0).state; got != sketchMultiplier {
		t.Errorf("seed 0 index 0 state = %d, want %d", got, uint32(sketchMultiplier))
	}
	if got := newSketcher(7, 0).state; got != 0x9E3779B6 {
		t.Errorf("seed 7 index 0 state = %#x", got)
	}
	s := newSketcher(7, 0)
	s.pass(vec{}, vec{x: 640})
	r := newSketcher(7, 0)
	for range 5 {
		r.next()
	}
	if s.state != r.state {
		t.Error("one pass must consume exactly five draws")
	}
}

func rectScene(items ...scene.Primitive) scene.Scene {
	return scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 12800, H: 3840}}, Groups: []*scene.Group{{Role: scene.GroupRoleNode, Items: items}}}
}

func TestSketchSpecVectors(t *testing.T) {
	line := rectScene(&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Points: []geom.Point{{X: 640, Y: 1920}, {X: 4480, Y: 1920}}})
	for _, seed := range []uint32{0, 7} {
		strokes := quadraticStrokes(t, sketchOutput(t, line, scene.Look{Kind: scene.LookHandDrawn, Seed: seed}))
		if len(strokes) != 2 {
			t.Fatalf("one straight segment must have two bowed strokes, got %d", len(strokes))
		}
		for _, stroke := range strokes {
			assertStrokeEnvelope(t, stroke)
		}
	}
}

func assertStrokeEnvelope(t *testing.T, stroke paintedElement) {
	t.Helper()
	var x0, y0, cx, cy, x1, y1 float64
	n, err := fmt.Sscanf(stroke.attrs["d"], "M %f %f Q %f %f %f %f", &x0, &y0, &cx, &cy, &x1, &y1)
	if err != nil || n != 6 {
		t.Fatalf("invalid quadratic stroke: %q", stroke.attrs["d"])
	}
	for _, bound := range [...]struct{ value, min, max float64 }{
		{x0, 9, 11}, {y0, 29, 31}, {x1, 69, 71},
		{y1, 29, 31}, {cx, 39, 41}, {cy, 28, 32},
	} {
		if bound.value < bound.min || bound.value > bound.max {
			t.Errorf("stroke leaves the specified endpoint jitter and bow envelope: %q", stroke.attrs["d"])
			break
		}
	}
}

func TestSketchKeepsFillAndSkipsCurves(t *testing.T) {
	frame := geom.Rect{X: 640, Y: 640, W: 3840, H: 2560}
	node := scene.Shape{Style: "node"}
	curved := []scene.Primitive{
		&scene.Ellipse{Shape: node, CX: 640, CY: 640, RX: 64, RY: 64},
		&scene.RoundRect{Shape: node, Rect: frame, R: 512},
		&scene.Path{Shape: node, Commands: []scene.Command{&scene.MoveTo{}, &scene.CubicTo{C1: geom.Point{X: 64}, C2: geom.Point{X: 64, Y: 64}, P: geom.Point{Y: 64}}, &scene.ClosePath{}}},
		&scene.Rect{Shape: scene.Shape{Style: "ink"}, Rect: frame},
	}
	look := scene.Look{Kind: scene.LookHandDrawn, Seed: 3}
	for _, p := range curved {
		if got, want := sketchOutput(t, rectScene(p), look), sketchOutput(t, rectScene(p), scene.Look{}); got != want {
			t.Errorf("%T was redrawn", p)
		}
	}
	got := sketchOutput(t, rectScene(&scene.Rect{Shape: node, Rect: frame}), look)
	assertSketchRectFill(t, got)
	assertSketchMarkerFill(t, look)
	straight := rectScene(&scene.Polyline{Shape: scene.Shape{Style: "edge"}, Corner: 512, Points: []geom.Point{{}, {X: 640}, {X: 640, Y: 640}}}, &scene.Path{Shape: scene.Shape{Style: "rule"}, Commands: []scene.Command{&scene.MoveTo{}, &scene.LineTo{P: geom.Point{X: 64}}, &scene.ClosePath{}}})
	if out := sketchOutput(t, straight, look); len(quadraticStrokes(t, out)) != 8 {
		t.Errorf("two open segments and two closed path segments must each draw twice: %s", out)
	}
}

func assertSketchRectFill(t *testing.T, got string) {
	t.Helper()
	fills := 0
	for _, element := range drawingElements(t, got) {
		if element.name == "rect" && element.attrs["x"] == "10" && element.attrs["y"] == "10" && element.attrs["width"] == "60" && element.attrs["height"] == "40" {
			assertFillWithoutOutline(t, element)
			fills++
		}
	}
	if fills != 1 || len(quadraticStrokes(t, got)) != 8 {
		t.Fatal("rectangle must retain one fill and two strokes per side")
	}
}

func assertFillWithoutOutline(t *testing.T, element paintedElement) {
	t.Helper()
	if element.paint["fill"] == "" || element.paint["fill"] == "none" || (element.paint["stroke"] != "" && element.paint["stroke"] != "none") {
		t.Errorf("rectangle must preserve its fill without a duplicate straight outline: %+v", element)
	}
}

func assertSketchMarkerFill(t *testing.T, look scene.Look) {
	t.Helper()
	marker := rectScene(&scene.MarkerRef{Marker: "point", At: geom.Point{X: 640, Y: 640}})
	plainMarker := drawingElements(t, sketchOutput(t, marker, scene.Look{}))
	sketchMarker := drawingElements(t, sketchOutput(t, marker, look))
	var plainPoints, sketchPoints string
	for _, element := range plainMarker {
		if element.name == "polygon" {
			plainPoints = element.attrs["points"]
		}
	}
	for _, element := range sketchMarker {
		if element.name == "polygon" && element.paint["fill"] != "none" {
			sketchPoints = element.attrs["points"]
		}
	}
	if plainPoints == "" || sketchPoints != plainPoints {
		t.Error("hand-drawn marker must retain its filled outline geometry")
	}
}

func assertClassicLook(t *testing.T, classic string) {
	t.Helper()
	if !strings.Contains(classic, "stroke-width='1'") || strings.Contains(classic, "stroke-width='2'") || !strings.Contains(classic, "rx='8'") {
		t.Fatal(classic)
	}
}

func assertNeoLook(t *testing.T, got string) {
	t.Helper()
	if strings.Contains(got, "stroke-width='1'") || !strings.Contains(got, "stroke-width='2'") || !strings.Contains(got, "rx='12' ry='12'") || strings.Contains(got, "rx='8'") {
		t.Fatal(got)
	}
}

func TestLookNeo(t *testing.T) {
	neo := scene.Look{Kind: scene.LookNeo}
	classic := sketchOutput(t, sample(), scene.Look{})
	got := sketchOutput(t, sample(), neo)
	assertClassicLook(t, classic)
	assertNeoLook(t, got)
	if strings.ReplaceAll(strings.ReplaceAll(got, "stroke-width='2'", "stroke-width='1'"), "rx='12' ry='12'", "rx='8' ry='8'") != classic {
		t.Error("neo must change only stroke widths and the radius token")
	}
	units := rectScene(&scene.Polyline{Shape: scene.Shape{Style: "rule", Width: scene.Width{Kind: scene.WidthUnits, Units: 192}}, Points: []geom.Point{{}, {X: 640}}}, &scene.RoundRect{Shape: scene.Shape{Style: "node"}, Rect: geom.Rect{W: 64, H: 64}, R: 256})
	if out := sketchOutput(t, units, neo); !strings.Contains(out, "stroke-width='3'") || !strings.Contains(out, "rx='4'") {
		t.Errorf("explicit widths and radii must stay: %s", out)
	}
}

func TestLookKeepsOtherOptions(t *testing.T) {
	var a, b bytes.Buffer
	if Write(&a, sample(), Options{Kind: "flowchart"}) != nil || Write(&b, sample(), Options{Kind: "flowchart", Look: scene.Look{Kind: scene.LookClassic, Seed: 9}}) != nil || a.String() != b.String() {
		t.Error("a classic look must ignore the seed")
	}
}
