package chart_test

import (
	"os"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const cynefinFull = "cynefin-beta\n  title Sorting\n  complex\n  \"probe\"\n  \"sense\"\n  complicated\n  \"analyse\"\n  clear\n  \"categorise\"\n  chaotic\n  \"act\"\n  confusion\n  \"unknown\"\n" +
	"  complex --> complicated : \"learned\"\n  clear --> chaotic\n"

func corpusFor(t *testing.T, kind string) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", kind, "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func cynefinScene(t *testing.T, source string, profile scene.Profile) scene.Scene {
	t.Helper()
	d := layout.ParseDiagram([]byte(source))
	require.Empty(t, errorsOf(d), source)
	in, err := d.Input(profile, scene.Options{})
	require.NoError(t, err)
	s, _, err := layout.Layout(in)
	require.NoError(t, err)
	return s
}

func errorsOf(d *layout.Diagram) []string {
	var out []string
	for _, diagnostic := range d.Diagnostics {
		if diagnostic.Severity == diag.SeverityError {
			out = append(out, diagnostic.Code)
		}
	}
	return out
}

func boxByID(t *testing.T, s scene.Scene, id string) scene.Box {
	t.Helper()
	for _, b := range s.Boxes {
		if b.ID == id {
			return b
		}
	}
	t.Fatalf("no box %s", id)
	return scene.Box{}
}

func TestCynefinAndInfoCorpusScenesAreValid(t *testing.T) {
	paths := append(corpusFor(t, "cynefin"), corpusFor(t, "info")...)
	paths = append(paths, filepath.Join("..", "..", "..", "corpus", "state", "mermaid", "state-diagram-v2~nightly-check~v2-should-render-a-simple-info.mmd"))
	for _, path := range paths {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			t.Run(filepath.Base(path)+"/"+profile.String(), func(t *testing.T) {
				d := layout.ParseDiagram(data)
				in, err := d.Input(profile, scene.Options{})
				require.NoError(t, err)
				s, _, err := layout.Layout(in)
				require.NoError(t, err)
				clause, failed, err := s.Validate()
				require.NoError(t, err)
				require.False(t, failed, clause.Message)
				if profile == scene.ProfileCell {
					result, err := cells.Render(s, cells.Options{})
					require.NoError(t, err)
					require.Zero(t, result.RefusedClusters)
				}
			})
		}
	}
}

func TestCynefinDomainBoxesStayInsideTheirQuadrant(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := cynefinScene(t, cynefinFull, profile)
		hw, hh := s.Canvas.W/2, s.Canvas.H/2
		complex, complicated := boxByID(t, s, "complex").Rect, boxByID(t, s, "complicated").Rect
		clear, chaotic := boxByID(t, s, "clear").Rect, boxByID(t, s, "chaotic").Rect
		require.LessOrEqual(t, complex.X+complex.W, hw)
		require.LessOrEqual(t, complex.Y+complex.H, hh)
		require.GreaterOrEqual(t, complicated.X, hw)
		require.LessOrEqual(t, complicated.Y+complicated.H, hh)
		require.GreaterOrEqual(t, clear.X, hw)
		require.GreaterOrEqual(t, clear.Y, hh)
		require.LessOrEqual(t, chaotic.X+chaotic.W, hw)
		require.GreaterOrEqual(t, chaotic.Y, hh)
	}
}

func TestCynefinConfusionSitsOnTheCentre(t *testing.T) {
	s := cynefinScene(t, cynefinFull, scene.ProfileVector)
	confusion := boxByID(t, s, "confusion").Rect
	centre := confusion.X + confusion.W/2
	require.InDelta(t, s.Canvas.W/2, centre, 1)
}

func TestCynefinKeepsDomainOrderAndAddsMissingDomains(t *testing.T) {
	s := cynefinScene(t, "cynefin-beta\nchaotic\n\"x\"\ncomplex\n", scene.ProfileVector)
	var ids []string
	for _, b := range s.Boxes {
		ids = append(ids, b.ID)
	}
	require.Equal(t, []string{"frame", "chaotic", "complex", "complicated", "clear", "confusion"}, ids)
}

func TestCynefinTransitionsBecomeOrthogonalRoutes(t *testing.T) {
	s := cynefinScene(t, cynefinFull, scene.ProfileVector)
	require.Len(t, s.Routes, 2)
	for _, r := range s.Routes {
		require.True(t, r.Orthogonal)
		require.GreaterOrEqual(t, len(r.Points), 2)
	}
	require.Equal(t, "complex", s.Routes[0].From)
	require.Equal(t, "chaotic", s.Routes[1].To)
	texts := textContents(s)
	require.True(t, texts["learned"])
	require.True(t, texts["Sorting"])
	require.True(t, texts["Confusion"])
}

func TestCynefinSelfLoopsAreDropped(t *testing.T) {
	s := cynefinScene(t, "cynefin-beta\ncomplex --> complex\ncomplex --> clear\n", scene.ProfileVector)
	require.Len(t, s.Routes, 1)
	require.Equal(t, "clear", s.Routes[0].To)
}

func foldPath(t *testing.T, s scene.Scene) *scene.Path {
	t.Helper()
	for _, item := range s.Groups[0].Items {
		if p, ok := item.(*scene.Path); ok && len(p.Commands) == 8 {
			return p
		}
	}
	t.Fatal("no fold path")
	return nil
}

func TestCynefinFoldIsDeterministicPerSeed(t *testing.T) {
	a := cynefinScene(t, "---\nconfig:\n  cynefin:\n    seed: 7\n---\n"+cynefinFull, scene.ProfileVector)
	b := cynefinScene(t, "---\nconfig:\n  cynefin:\n    seed: 7\n---\n"+cynefinFull, scene.ProfileVector)
	c := cynefinScene(t, "---\nconfig:\n  cynefin:\n    seed: 8\n---\n"+cynefinFull, scene.ProfileVector)
	require.Equal(t, foldPath(t, a), foldPath(t, b))
	require.NotEqual(t, foldPath(t, a), foldPath(t, c))
}

func TestCynefinZeroAmplitudeFoldIsStraight(t *testing.T) {
	s := cynefinScene(t, "---\nconfig:\n  cynefin:\n    boundaryAmplitude: 0\n---\n"+cynefinFull, scene.ProfileVector)
	fold := foldPath(t, s)
	cx := s.Canvas.W / 2
	for _, command := range fold.Commands {
		switch v := command.(type) {
		case *scene.MoveTo:
			require.EqualValues(t, cx, v.P.X)
		case *scene.CubicTo:
			require.EqualValues(t, cx, v.P.X)
			require.EqualValues(t, cx, v.C1.X)
			require.EqualValues(t, cx, v.C2.X)
		}
	}
}

func TestCynefinCanvasGrowsToHoldOverflow(t *testing.T) {
	var b strings.Builder
	b.WriteString("---\nconfig:\n  cynefin:\n    width: 200\n    height: 120\n---\ncynefin-beta\ncomplex\n")
	for range 12 {
		b.WriteString("\"a very long item label that overflows the quadrant\"\n")
	}
	s := cynefinScene(t, b.String(), scene.ProfileVector)
	complex := boxByID(t, s, "complex").Rect
	require.LessOrEqual(t, complex.Y+complex.H, s.Canvas.H)
	require.Greater(t, s.Canvas.H, int32(120*64))
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
}

func TestCynefinConfigOverridesCanvasInEachProfile(t *testing.T) {
	src := "---\nconfig:\n  cynefin:\n    width: 640\n    height: 480\n---\ncynefin-beta\n"
	vector := cynefinScene(t, src, scene.ProfileVector)
	require.EqualValues(t, 640*64, vector.Canvas.W)
	require.EqualValues(t, 480*64, vector.Canvas.H)
	cell := cynefinScene(t, src, scene.ProfileCell)
	require.EqualValues(t, 80, cell.Canvas.W)
	require.EqualValues(t, 30, cell.Canvas.H)
}

func TestCynefinDecorHoldsQuadrantsFoldDividersCliffAndEllipse(t *testing.T) {
	s := cynefinScene(t, cynefinFull, scene.ProfileVector)
	require.Equal(t, scene.GroupRoleDecor, s.Groups[0].Role)
	var rects, paths, lines, ellipses int
	for _, item := range s.Groups[0].Items {
		switch item.(type) {
		case *scene.Rect:
			rects++
		case *scene.Path:
			paths++
		case *scene.Polyline:
			lines++
		case *scene.Ellipse:
			ellipses++
		}
	}
	require.Equal(t, []int{4, 2, 2, 1}, []int{rects, paths, lines, ellipses})
}

func TestInfoSceneShowsTheVersionInBothProfiles(t *testing.T) {
	vector := cynefinScene(t, "info\n", scene.ProfileVector)
	require.EqualValues(t, 400*64, vector.Canvas.W)
	require.EqualValues(t, 100*64, vector.Canvas.H)
	require.True(t, textContents(vector)["v0.1.0"])
	cell := cynefinScene(t, "info showInfo\n", scene.ProfileCell)
	require.EqualValues(t, 6, cell.Canvas.W)
	require.EqualValues(t, 1, cell.Canvas.H)
	require.Equal(t, "info", cell.Boxes[0].ID)
	require.Equal(t, []string{"v0.1.0"}, cell.Labels[0].Lines)
}

const cynefinDense = "cynefin-beta\n  complex\n  \"alpha\"\n  complicated\n  \"beta\"\n  clear\n  \"gamma\"\n  chaotic\n  \"delta\"\n  confusion\n  \"epsilon\"\n" +
	"  complex --> clear : \"diagonal one\"\n  complicated --> chaotic : \"diagonal two\"\n  clear --> complex\n  chaotic --> complicated\n  complex --> confusion : \"in\"\n  confusion --> clear : \"out\"\n"

func routeHitsBox(points []geom.Point, box geom.Rect) bool {
	for i := 1; i < len(points); i++ {
		a, b := points[i-1], points[i]
		if min(a.X, b.X) <= box.X+box.W && max(a.X, b.X) >= box.X && min(a.Y, b.Y) <= box.Y+box.H && max(a.Y, b.Y) >= box.Y {
			return true
		}
	}
	return false
}

func TestCynefinRoutesAvoidTheOtherDomainBoxes(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := cynefinScene(t, cynefinDense, profile)
		require.Len(t, s.Routes, 6)
		for _, route := range s.Routes {
			for _, b := range s.Boxes {
				if b.ID == "frame" || b.ID == route.From || b.ID == route.To {
					continue
				}
				require.False(t, routeHitsBox(route.Points, b.Rect), "%v route %s crosses box %s", profile, route.ID, b.ID)
			}
		}
	}
}

func TestCynefinDenseCellRenderKeepsEveryLabel(t *testing.T) {
	s := cynefinScene(t, cynefinDense, scene.ProfileCell)
	result, err := cells.Render(s, cells.Options{})
	require.NoError(t, err)
	require.Zero(t, result.RefusedClusters)
	rows := strings.Split(string(result.Text), "\n")
	for _, l := range s.Labels {
		row := []rune(rows[l.Rect.Y])
		require.GreaterOrEqual(t, len(row), int(l.Rect.X+l.Rect.W), "label %s", l.ID)
		require.Equal(t, strings.Join(l.Lines, ""), string(row[l.Rect.X:l.Rect.X+l.Rect.W]), "label %s", l.ID)
	}
}

func TestCynefinRouteLabelsAvoidDomainBoxes(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := cynefinScene(t, cynefinDense, profile)
		for _, l := range s.Labels {
			if !strings.HasPrefix(l.ID, "e") {
				continue
			}
			for _, b := range s.Boxes {
				if b.ID == "frame" {
					continue
				}
				apart := l.Rect.X+l.Rect.W <= b.Rect.X || b.Rect.X+b.Rect.W <= l.Rect.X || l.Rect.Y+l.Rect.H <= b.Rect.Y || b.Rect.Y+b.Rect.H <= l.Rect.Y
				require.True(t, apart, "%v label %s overlaps box %s", profile, l.ID, b.ID)
			}
		}
	}
}
