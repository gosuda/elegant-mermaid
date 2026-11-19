package svg

import (
	"errors"
	"io"
	"regexp"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
)

func triangleFont(width int32) scenelink.Font {
	triangle := scenelink.Glyph{Rune: 'A', Advance: 600, Commands: []scenelink.Command{
		{Op: scenelink.OpMoveTo, Points: [3][2]int32{{0, 0}}},
		{Op: scenelink.OpLineTo, Points: [3][2]int32{{width, 0}}},
		{Op: scenelink.OpLineTo, Points: [3][2]int32{{width / 2, 700}}},
	}}
	curve := scenelink.Glyph{Rune: 'B', Advance: 500, Commands: []scenelink.Command{
		{Op: scenelink.OpMoveTo, Points: [3][2]int32{{0, 0}}},
		{Op: scenelink.OpQuadTo, Points: [3][2]int32{{250, 500}, {500, 0}}},
		{Op: scenelink.OpMoveTo, Points: [3][2]int32{{100, 100}}},
		{Op: scenelink.OpCubeTo, Points: [3][2]int32{{150, 300}, {250, 300}, {300, 100}}},
	}}
	return scenelink.Font{UnitsPerEm: 1000, Glyphs: []scenelink.Glyph{triangle, curve}}
}

func testOutlines() *scenelink.Outlines {
	return &scenelink.Outlines{triangleFont(500), triangleFont(1000)}
}

func textScene(role scene.TextRole, align scene.Align, runs ...scene.Run) scene.Scene {
	text := &scene.Text{Rect: geom.Rect{X: 640, Y: 640, W: 3200, H: 1280}, Role: role, Size: 10, Align: align, Style: "text", Lines: [][]scene.Run{runs}}
	return scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 6400, H: 2560}}, Groups: []*scene.Group{{Role: scene.GroupRoleNode, Items: []scene.Primitive{text}}}}
}

func writePaths(t *testing.T, s scene.Scene) string {
	t.Helper()
	var out strings.Builder
	if err := Write(&out, s, Options{Text: TextPaths, Outlines: testOutlines()}); err != nil {
		t.Fatal(err)
	}
	return out.String()
}

func labelPath(t *testing.T, role scene.TextRole, align scene.Align, runs ...scene.Run) string {
	t.Helper()
	return textPathData(t, writePaths(t, textScene(role, align, runs...)))
}

func textPathData(t *testing.T, doc string) string {
	t.Helper()
	m := regexp.MustCompile(`<path class='emd-s-text' d='([^']*)'/>`).FindAllStringSubmatch(doc, -1)
	if len(m) != 1 {
		t.Fatalf("want one text path, got %d in:\n%s", len(m), doc)
	}
	return m[0][1]
}

func TestTextPathsPlacement(t *testing.T) {
	doc := writePaths(t, textScene(scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "AA"}))
	want := "M10 23.5L15 23.5L12.5 16.5ZM16 23.5L21 23.5L18.5 16.5Z"
	if got := textPathData(t, doc); got != want {
		t.Fatalf("path data %q, want %q", got, want)
	}
	if strings.Contains(doc, "<text") || strings.Contains(doc, "<tspan") {
		t.Fatalf("text elements remain:\n%s", doc)
	}
	if !strings.Contains(doc, ".emd-s-text{fill:") {
		t.Fatalf("text style rule missing:\n%s", doc)
	}
}

func TestTextPathsAlignment(t *testing.T) {
	start := labelPath(t, scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "A"})
	middle := labelPath(t, scene.TextRoleBody, scene.AlignMiddle, scene.Run{Text: "A"})
	end := labelPath(t, scene.TextRoleBody, scene.AlignEnd, scene.Run{Text: "A"})
	for name, c := range map[string]struct{ got, want string }{
		"start":  {start, "M10 23.5L15 23.5L12.5 16.5Z"},
		"middle": {middle, "M32 23.5L37 23.5L34.5 16.5Z"},
		"end":    {end, "M54 23.5L59 23.5L56.5 16.5Z"},
	} {
		if c.got != c.want {
			t.Errorf("%s: %q, want %q", name, c.got, c.want)
		}
	}
}

func TestTextPathsWeightAndItalic(t *testing.T) {
	regular := labelPath(t, scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "A"})
	label := labelPath(t, scene.TextRoleLabel, scene.AlignStart, scene.Run{Text: "A"})
	bold := labelPath(t, scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "A", Bold: true})
	italic := labelPath(t, scene.TextRoleLabel, scene.AlignStart, scene.Run{Text: "A", Italic: true})
	if regular != "M10 23.5L15 23.5L12.5 16.5Z" || label != "M10 23.5L20 23.5L15 16.5Z" || bold != label {
		t.Fatalf("weights: regular %q, label %q, bold %q", regular, label, bold)
	}
	if italic != "M10 23.5L15 23.5L13.92 16.5Z" {
		t.Fatalf("italic runs use the weight 400 outlines sheared by 13/64 of the height: got %q", italic)
	}
}

func TestTextPathsCurvesCloseEachContour(t *testing.T) {
	d := labelPath(t, scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "B"})
	want := "M10 23.5Q12.5 18.5 15 23.5ZM11 22.5C11.5 20.5 12.5 20.5 13 22.5Z"
	if d != want {
		t.Fatalf("path data %q, want %q", d, want)
	}
}

func TestTextPathsMissingGlyphKeepsAdvance(t *testing.T) {
	spaced := labelPath(t, scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "A A"})
	tight := labelPath(t, scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "AA"})
	if spaced != "M10 23.5L15 23.5L12.5 16.5ZM22 23.5L27 23.5L24.5 16.5Z" || spaced == tight {
		t.Fatalf("a codepoint without an outline must keep its advance: %q vs %q", spaced, tight)
	}
	empty := writePaths(t, textScene(scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "   "}))
	if strings.Contains(empty, "<path class='emd-s-text'") || strings.Contains(empty, "emd-s-text{") {
		t.Fatalf("an outline-free label drew a path:\n%s", empty)
	}
}

func TestTextPathsRequireOutlines(t *testing.T) {
	s := textScene(scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "A"})
	for name, o := range map[string]Options{
		"nil":      {Text: TextPaths},
		"zero":     {Text: TextPaths, Outlines: &scenelink.Outlines{}},
		"one font": {Text: TextPaths, Outlines: &scenelink.Outlines{triangleFont(500), {}}},
		"mode":     {Text: TextMode(7), Outlines: testOutlines()},
	} {
		if err := Write(io.Discard, s, o); err == nil {
			t.Errorf("%s: accepted", name)
		} else if _, ok := errors.AsType[*ConfigError](err); !ok {
			t.Errorf("%s: %v", name, err)
		}
	}
}

func TestTextFontIgnoresOutlines(t *testing.T) {
	var out strings.Builder
	if err := Write(&out, textScene(scene.TextRoleBody, scene.AlignStart, scene.Run{Text: "A"}), Options{Outlines: testOutlines()}); err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(out.String(), "<text ") || strings.Contains(out.String(), "<path class='emd-s-text'") {
		t.Fatalf("font mode must keep <text>:\n%s", out.String())
	}
}
