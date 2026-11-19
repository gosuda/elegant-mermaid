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
	"github.com/gosuda/elegant-mermaid/internal/layout/chart"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func quadrantFiles(t *testing.T) []string {
	t.Helper()
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "quadrant", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	slices.Sort(paths)
	return paths
}

func boxOf(t *testing.T, s scene.Scene, id string) geom.Rect {
	t.Helper()
	for _, b := range s.Boxes {
		if b.ID == id {
			return b.Rect
		}
	}
	require.FailNow(t, "missing box "+id)
	return geom.Rect{}
}

func ellipses(s scene.Scene) []*scene.Ellipse {
	var out []*scene.Ellipse
	for _, g := range s.Groups {
		for _, item := range g.Items {
			if e, ok := item.(*scene.Ellipse); ok {
				out = append(out, e)
			}
		}
	}
	return out
}

func hasError(d *layout.Diagram) bool {
	return slices.ContainsFunc(d.Diagnostics, func(x diag.Diagnostic) bool { return x.Severity == diag.SeverityError })
}

func TestQuadrantCorpusScenesAreValid(t *testing.T) {
	accepted := 0
	for _, path := range quadrantFiles(t) {
		data, err := os.ReadFile(path)
		require.NoError(t, err)
		d := layout.ParseDiagram(data)
		if hasError(d) {
			continue
		}
		accepted++
		for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
			in, err := d.Input(profile, scene.Options{})
			require.NoError(t, err, path)
			s, _, err := layout.Layout(in)
			require.NoError(t, err, path)
			clause, failed, err := s.Validate()
			require.NoError(t, err, path)
			require.False(t, failed, "%s %s: %s", path, profile, clause.Message)
			if profile == scene.ProfileCell {
				result, err := cells.Render(s, cells.Options{})
				require.NoError(t, err)
				require.Zero(t, result.RefusedClusters, path)
			}
		}
	}
	require.Greater(t, accepted, 20)
}

func TestQuadrantTilesPartitionThePlot(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := sceneOf(t, "quadrantChart\n  x-axis A --> B\n  y-axis C --> D\n  quadrant-1 one\n", profile)
		plot := boxOf(t, s, "plot")
		var area int64
		var tiles []geom.Rect
		for _, id := range []string{"q1", "q2", "q3", "q4"} {
			r := boxOf(t, s, id)
			area += int64(r.W) * int64(r.H)
			tiles = append(tiles, r)
		}
		require.Equal(t, int64(plot.W)*int64(plot.H), area, profile.String())
		for i := range tiles {
			for j := range i {
				hit, err := geom.Intersects(tiles[i], tiles[j])
				require.NoError(t, err)
				require.False(t, hit)
			}
		}
		q1, q2, q3, q4 := boxOf(t, s, "q1"), boxOf(t, s, "q2"), boxOf(t, s, "q3"), boxOf(t, s, "q4")
		require.Greater(t, q1.X, q2.X)
		require.Equal(t, q1.Y, q2.Y)
		require.Equal(t, q3.X, q2.X)
		require.Greater(t, q3.Y, q2.Y)
		require.Equal(t, q4.X, q1.X)
		require.Equal(t, q4.Y, q3.Y)
	}
}

func TestQuadrantVectorPointsFollowTheUnitSquare(t *testing.T) {
	s := sceneOf(t, "quadrantChart\n  A: [0, 0]\n  B: [1, 1]\n  C: [0.5, 0.25]\n", scene.ProfileVector)
	plot := boxOf(t, s, "plot")
	dots := ellipses(s)
	require.Len(t, dots, 3)
	want := [][2]int64{
		{int64(plot.X), int64(plot.Y + plot.H)},
		{int64(plot.X + plot.W), int64(plot.Y)},
		{int64(plot.X) + geom.FloorDiv(500*int64(plot.W), 1000), int64(plot.Y+plot.H) - geom.FloorDiv(250*int64(plot.H), 1000)},
	}
	for i, e := range dots {
		require.Equal(t, want[i], [2]int64{int64(e.CX), int64(e.CY)}, "point %d", i)
		require.Equal(t, int32(320), e.RX)
		require.Equal(t, int32(320), e.RY)
	}
}

func TestQuadrantCellPointsStayInsideTheFrame(t *testing.T) {
	s := sceneOf(t, "quadrantChart\n  A: [0, 0]\n  B: [1, 1]\n", scene.ProfileCell)
	plot := boxOf(t, s, "plot")
	for _, e := range ellipses(s) {
		require.Greater(t, e.CX, plot.X)
		require.Less(t, e.CX, plot.X+plot.W-1)
		require.Greater(t, e.CY, plot.Y)
		require.Less(t, e.CY, plot.Y+plot.H-1)
	}
}

func TestQuadrantConfigSetsTheCanvas(t *testing.T) {
	source := "%%{init: {\"quadrantChart\": {\"chartWidth\": 800, \"chartHeight\": 600}}}%%\nquadrantChart\n  A: [0.5, 0.5]\n"
	s := sceneOf(t, source, scene.ProfileVector)
	require.Equal(t, int32(800*64), s.Canvas.W)
	require.Equal(t, int32(600*64), s.Canvas.H)
	cell := sceneOf(t, source, scene.ProfileCell)
	require.Equal(t, int32(100), cell.Canvas.W)
	require.Equal(t, int32(38), cell.Canvas.H)
}

func TestQuadrantLabelsAvoidDividersInCells(t *testing.T) {
	source := "quadrantChart\n  title T\n  x-axis Low --> High\n  y-axis Low --> High\n  Centre point label: [0.5, 0.5]\n  Wide label near the edge: [0.95, 0.9]\n"
	s := sceneOf(t, source, scene.ProfileCell)
	result, err := cells.Render(s, cells.Options{})
	require.NoError(t, err)
	require.Zero(t, result.RefusedClusters)
	for _, label := range s.Labels {
		require.NotEmpty(t, label.Lines, label.ID)
	}
}

func TestQuadrantWithoutLabelsStillLaysOut(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := sceneOf(t, "quadrantChart\n", profile)
		require.Empty(t, s.Labels)
		require.Len(t, s.Boxes, 5)
		clause, failed, err := s.Validate()
		require.NoError(t, err)
		require.False(t, failed, clause.Message)
	}
}

func TestQuadrantSkeletonMatchesTheLaidOutIDs(t *testing.T) {
	q := &chart.Quadrant{Title: "T", Tiles: [4]string{"a", "", "c", ""}, XLeft: "l", Points: []chart.QuadrantPoint{{X: 1, Y: 2, Radius: chart.NoPointRadius, Label: "p"}}}
	skeleton := chart.QuadrantSkeleton(q)
	var boxes, labels []string
	for _, b := range skeleton.Boxes {
		boxes = append(boxes, b.ID)
	}
	for _, l := range skeleton.Labels {
		labels = append(labels, l.ID)
	}
	require.Equal(t, "plot,q1,q2,q3,q4,p0", strings.Join(boxes, ","))
	require.Equal(t, "title,x.left,q1.label,q3.label,p0.label", strings.Join(labels, ","))
}
