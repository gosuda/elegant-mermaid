package raster

import (
	"bytes"
	"errors"
	"image"
	"regexp"
	"strconv"
	"strings"
	"testing"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
	"github.com/gosuda/elegant-mermaid/internal/svg"
	"github.com/gosuda/elegant-mermaid/internal/theme"
	"golang.org/x/image/font/sfnt"
	"golang.org/x/image/vector"
)

const demoSource = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n"

func TestGlyphOpsMatchSfnt(t *testing.T) {
	for name, pair := range map[string][2]uint8{
		"move":  {scenelink.OpMoveTo, uint8(sfnt.SegmentOpMoveTo)},
		"line":  {scenelink.OpLineTo, uint8(sfnt.SegmentOpLineTo)},
		"quad":  {scenelink.OpQuadTo, uint8(sfnt.SegmentOpQuadTo)},
		"cubic": {scenelink.OpCubeTo, uint8(sfnt.SegmentOpCubeTo)},
	} {
		if pair[0] != pair[1] {
			t.Errorf("%s: scenelink op %d differs from sfnt op %d", name, pair[0], pair[1])
		}
	}
}

func TestRenderSVGTextPaths(t *testing.T) {
	ctx := t.Context()
	font, err := mermaid.RenderSVGSource(ctx, []byte(demoSource), mermaid.SVGOptions{})
	if err != nil || !bytes.Contains(font, []byte("<text ")) {
		t.Fatalf("font mode: %v", err)
	}
	paths, err := mermaid.RenderSVGSource(ctx, []byte(demoSource), mermaid.SVGOptions{Text: mermaid.TextPaths, Outlines: InterOutlines()})
	if err != nil {
		t.Fatal(err)
	}
	doc := string(paths)
	if strings.Contains(doc, "<text") || strings.Count(doc, "<path class='emd-s-text' d='M") != 5 {
		t.Fatalf("paths mode must draw each of the five labels as one path and no <text>:\n%s", doc)
	}
	ignored, err := mermaid.RenderSVGSource(ctx, []byte(demoSource), mermaid.SVGOptions{Outlines: InterOutlines()})
	if err != nil || !bytes.Equal(ignored, font) {
		t.Fatalf("outlines must be ignored in font mode: %v", err)
	}
}

func TestRenderSVGTextPathsRequireOutlines(t *testing.T) {
	for name, o := range map[string]mermaid.SVGOptions{
		"nil":   {Text: mermaid.TextPaths},
		"empty": {Text: mermaid.TextPaths, Outlines: &mermaid.GlyphOutlines{}},
		"mode":  {Text: mermaid.TextMode(9), Outlines: InterOutlines()},
	} {
		_, err := mermaid.RenderSVGSource(t.Context(), []byte(demoSource), o)
		if !errors.Is(err, mermaid.ErrBadConfig) {
			t.Errorf("%s: %v", name, err)
		}
	}
}

func TestSVGTextPathsMatchRaster(t *testing.T) {
	label := &scene.Text{Rect: geom.Rect{X: 640, Y: 640, W: 12800, H: 2560}, Role: scene.TextRoleBody, Size: 14, Align: scene.AlignMiddle, Style: "text", Lines: [][]scene.Run{
		{{Text: "Hello, "}, {Text: "bold", Bold: true}, {Text: " italic Wg", Italic: true}},
		{{Text: "second line of text"}},
	}}
	s := scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 14080, H: 3840}}, Groups: []*scene.Group{{Role: scene.GroupRoleNode, Items: []scene.Primitive{label}}}}
	fonts, ok := scenelink.OutlinesOf(InterOutlines())
	if !ok {
		t.Fatal("no embedded outlines")
	}
	var doc strings.Builder
	if err := svg.Write(&doc, s, svg.Options{Text: svg.TextPaths, Outlines: &fonts}); err != nil {
		t.Fatal(err)
	}
	const scale = 2
	pixels, err := drawScene(s, RGBAOptions{Options: Options{Scale: scale}})
	if err != nil {
		t.Fatal(err)
	}
	coverage := svgCoverage(t, doc.String(), pixels.Bounds(), scale)
	assertSameCoverage(t, pixels, coverage)
}

func svgCoverage(t *testing.T, doc string, bounds image.Rectangle, scale float64) *image.Alpha {
	t.Helper()
	m := regexp.MustCompile(`<path class='emd-s-text' d='([^']*)'/>`).FindStringSubmatch(doc)
	if m == nil {
		t.Fatalf("no text path in:\n%s", doc)
	}
	z := vector.NewRasterizer(bounds.Dx(), bounds.Dy())
	drawPathData(t, z, m[1], float32(scale))
	out := image.NewAlpha(bounds)
	z.Draw(out, bounds, image.Opaque, image.Point{})
	return out
}

func drawPathData(t *testing.T, z *vector.Rasterizer, d string, scale float32) {
	t.Helper()
	tokens := regexp.MustCompile(`[MLQCZ]|-?[0-9]+(?:\.[0-9]+)?`).FindAllString(d, -1)
	args := map[string]int{"M": 2, "L": 2, "Q": 4, "C": 6, "Z": 0}
	for i := 0; i < len(tokens); {
		op := tokens[i]
		n, known := args[op]
		if !known || i+1+n > len(tokens) {
			t.Fatalf("bad path data near %q", op)
		}
		v := make([]float32, n)
		for j := range n {
			f, err := strconv.ParseFloat(tokens[i+1+j], 32)
			if err != nil {
				t.Fatal(err)
			}
			v[j] = float32(f) * scale
		}
		switch op {
		case "M":
			z.MoveTo(v[0], v[1])
		case "L":
			z.LineTo(v[0], v[1])
		case "Q":
			z.QuadTo(v[0], v[1], v[2], v[3])
		case "C":
			z.CubeTo(v[0], v[1], v[2], v[3], v[4], v[5])
		default:
			z.ClosePath()
		}
		i += 1 + n
	}
}

func assertSameCoverage(t *testing.T, pixels *image.RGBA, coverage *image.Alpha) {
	t.Helper()
	th, err := theme.Resolve("")
	if err != nil {
		t.Fatal(err)
	}
	bg, ink := th.Colour(theme.Background), th.Colour(theme.Foreground)
	span := float64(int(bg.R) - int(ink.R))
	inked, worst := 0, 0.0
	for y := pixels.Bounds().Min.Y; y < pixels.Bounds().Max.Y; y++ {
		for x := pixels.Bounds().Min.X; x < pixels.Bounds().Max.X; x++ {
			raster := float64(int(bg.R)-int(pixels.RGBAAt(x, y).R)) / span
			vectorised := float64(coverage.AlphaAt(x, y).A) / 255
			if raster > 0.5 {
				inked++
			}
			worst = max(worst, absFloat(raster-vectorised))
		}
	}
	if inked < 100 {
		t.Fatalf("only %d inked pixels; the text did not render", inked)
	}
	if worst > 0.12 {
		t.Fatalf("SVG text path and raster text differ by %.3f of full coverage", worst)
	}
}

func absFloat(v float64) float64 {
	if v < 0 {
		return -v
	}
	return v
}
