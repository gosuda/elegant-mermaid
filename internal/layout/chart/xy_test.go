package chart_test

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func box(t *testing.T, s scene.Scene, id string) scene.Box {
	t.Helper()
	for _, b := range s.Boxes {
		if b.ID == id {
			return b
		}
	}
	t.Fatalf("no box %s", id)
	return scene.Box{}
}

func label(t *testing.T, s scene.Scene, id string) scene.Label {
	t.Helper()
	for _, l := range s.Labels {
		if l.ID == id {
			return l
		}
	}
	t.Fatalf("no label %s", id)
	return scene.Label{}
}

func shown(l scene.Label) bool { return l.Rect.W != 0 || l.Rect.H != 0 }

func TestCanvasIsTheConfiguredSize(t *testing.T) {
	s := sceneOf(t, "xychart\nbar [1]\n", scene.ProfileVector)
	require.Equal(t, geom.Size{W: 700 * 64, H: 500 * 64}, s.Canvas)
	s = sceneOf(t, "xychart\nbar [1]\n", scene.ProfileCell)
	require.Equal(t, geom.Size{W: 88, H: 32}, s.Canvas)
	s = sceneOf(t, "---\nconfig:\n  xyChart:\n    width: 1000\n    height: 320\n---\nxychart\nbar [1]\n", scene.ProfileVector)
	require.Equal(t, geom.Size{W: 1000 * 64, H: 320 * 64}, s.Canvas)
	s = sceneOf(t, "---\nconfig:\n  xyChart:\n    width: 1000\n    height: 320\n---\nxychart\nbar [1]\n", scene.ProfileCell)
	require.Equal(t, geom.Size{W: 125, H: 20}, s.Canvas)
}

func TestBarWidthFollowsTheOuterPaddingRule(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := sceneOf(t, "xychart\nx-axis [a, b]\nbar [1, 2]\n", profile)
		plot, first, second := box(t, s, "plot").Rect, box(t, s, "p0.b0").Rect, box(t, s, "p0.b1").Rect
		half := first.W / 2
		outer := int64(first.X+half) - int64(plot.X)
		require.Equal(t, outer, int64(plot.X+plot.W)-int64(second.X+half))
		tickDistance := (int64(plot.W) - 2*outer) / 2
		want := min(2*outer, tickDistance) * 950 / 1000
		if profile == scene.ProfileCell {
			want = max(want, 1)
		}
		require.Equal(t, want, int64(first.W), profile.String())
		require.Equal(t, first.W, second.W)
	}
}

func TestBarsRaiseTheOuterPaddingToSeventyPercentOfATick(t *testing.T) {
	s := sceneOf(t, "---\nconfig:\n  xyChart:\n    xAxis:\n      showLabel: false\n---\nxychart\nx-axis [a, b]\nbar [1, 2]\n", scene.ProfileVector)
	plot, first := box(t, s, "plot").Rect, box(t, s, "p0.b0").Rect
	outer := int64(first.X+first.W/2) - int64(plot.X)
	require.Equal(t, int64(plot.W)/2*700/2000, outer)
}

func TestLineBoxesCoverTheirPointsInsideThePlot(t *testing.T) {
	s := sceneOf(t, "xychart\nx-axis [a, b, c]\nline [1, 5, 3]\n", scene.ProfileVector)
	plot, line := box(t, s, "plot").Rect, box(t, s, "p0").Rect
	require.Equal(t, "plot", box(t, s, "p0").Parent)
	for _, inside := range []bool{line.X >= plot.X, line.Y >= plot.Y, line.X+line.W <= plot.X+plot.W, line.Y+line.H <= plot.Y+plot.H} {
		require.True(t, inside)
	}
	require.Positive(t, line.W)
	require.Positive(t, line.H)
}

func TestValuesOutsideTheExplicitRangeStayInsideThePlot(t *testing.T) {
	for _, profile := range []scene.Profile{scene.ProfileVector, scene.ProfileCell} {
		s := sceneOf(t, "xychart\nx-axis [a, b]\ny-axis 0 --> 10\nbar [500, -500]\n", profile)
		plot := box(t, s, "plot").Rect
		for _, id := range []string{"p0.b0", "p0.b1"} {
			b := box(t, s, id).Rect
			require.GreaterOrEqual(t, b.Y, plot.Y)
			require.LessOrEqual(t, b.Y+b.H, plot.Y+plot.H)
		}
	}
}

func TestAbsentValuesHaveNoBoxAndBreakTheLine(t *testing.T) {
	s := sceneOf(t, "xychart\nx-axis [a, b, c]\nbar [1]\nline [1, 2, 3]\n", scene.ProfileVector)
	var ids []string
	for _, b := range s.Boxes {
		ids = append(ids, b.ID)
	}
	require.Equal(t, []string{"plot", "p0.b0", "p1"}, ids)
}

func TestHorizontalOrientationPutsCategoriesLeftAndValuesOnTop(t *testing.T) {
	s := sceneOf(t, "xychart horizontal\nx-axis [first, second]\ny-axis 0 --> 10\nbar [3, 7]\n", scene.ProfileVector)
	plot := box(t, s, "plot").Rect
	category, value := label(t, s, "x.t0").Rect, label(t, s, "y.t0").Rect
	require.Less(t, category.X+category.W, plot.X)
	require.Less(t, value.Y+value.H, plot.Y+1)
	require.LessOrEqual(t, plot.X, box(t, s, "p0.b0").Rect.X)
	longer, shorter := box(t, s, "p0.b1").Rect, box(t, s, "p0.b0").Rect
	require.Greater(t, longer.W, shorter.W)
	require.Equal(t, shorter.X, longer.X)
}

func TestHiddenXAxisLabelsKeepZeroRectangles(t *testing.T) {
	s := sceneOf(t, "---\nconfig:\n  xyChart:\n    xAxis:\n      showLabel: false\n---\nxychart\nx-axis [a, b]\nbar [1, 2]\n", scene.ProfileVector)
	require.False(t, shown(label(t, s, "x.t0")))
	require.True(t, shown(label(t, s, "y.t0")))
}

func TestChartTitleIsDroppedWhenTheChartIsTooShort(t *testing.T) {
	short := "---\nconfig:\n  xyChart:\n    height: 40\n---\nxychart\ntitle \"T\"\nbar [1]\n"
	require.False(t, shown(label(t, sceneOf(t, short, scene.ProfileVector), "title")))
	require.True(t, shown(label(t, sceneOf(t, strings.Replace(short, "height: 40", "height: 500", 1), scene.ProfileVector), "title")))
}

func TestPlotsWithoutTitlesGetNumberedLegendLabels(t *testing.T) {
	s := sceneOf(t, "xychart\nx-axis [a]\nbar [1]\nline \"Named\" [2]\nbar [3]\n", scene.ProfileVector)
	require.Equal(t, "Series 1", label(t, s, "legend.0").Text)
	require.Equal(t, "Named", label(t, s, "legend.1").Text)
	require.Equal(t, "Series 3", label(t, s, "legend.2").Text)
	require.True(t, shown(label(t, s, "legend.0")))
}

func TestLegendThatDoesNotFitBesideThePlotOverlaysIt(t *testing.T) {
	src := "---\nconfig:\n  xyChart:\n    width: 120\n---\nxychart\nx-axis [a]\nbar \"a very long series title indeed\" [1]\n"
	s := sceneOf(t, src, scene.ProfileVector)
	plot, legend := box(t, s, "plot").Rect, label(t, s, "legend.0")
	require.True(t, shown(legend))
	require.Equal(t, plot.X+plot.W, s.Canvas.W)
	require.GreaterOrEqual(t, legend.Rect.X, int32(0))
	require.Less(t, legend.Rect.X, plot.X+plot.W)
}

func TestLegendBesideThePlotTakesItsWidth(t *testing.T) {
	s := sceneOf(t, "xychart\nx-axis [a]\nbar \"S\" [1]\n", scene.ProfileVector)
	plot, legend := box(t, s, "plot").Rect, label(t, s, "legend.0")
	require.GreaterOrEqual(t, legend.Rect.X, plot.X+plot.W)
	require.Less(t, plot.X+plot.W, s.Canvas.W)
}

func TestTickLabelsOfTheCellProfileNeverOverlap(t *testing.T) {
	s := sceneOf(t, "---\nconfig:\n  xyChart:\n    height: 40\n---\nxychart\nx-axis [a, b]\nbar [1, 2000]\n", scene.ProfileCell)
	rows := map[int32]bool{}
	for _, l := range s.Labels {
		if strings.HasPrefix(l.ID, "y.t") && shown(l) {
			require.False(t, rows[l.Rect.Y])
			rows[l.Rect.Y] = true
		}
	}
	require.NotEmpty(t, rows)
}

func TestOverflowingValuesAreRejected(t *testing.T) {
	d := parseFor(t, "xychart\nx-axis [a]\nbar [99999999999]\n")
	_, err := inputAndLayout(d)
	require.Error(t, err)
}

func TestPlotKeepsAnEdgeCellOnAOneRowCellCanvas(t *testing.T) {
	s := sceneOf(t, "---\nconfig:\n  xyChart:\n    height: 1\n---\nxychart\nline [0]\n", scene.ProfileCell)
	plot, line := box(t, s, "plot").Rect, box(t, s, "p0").Rect
	require.Equal(t, int32(1), plot.H)
	require.Equal(t, int32(1), s.Canvas.H)
	require.GreaterOrEqual(t, line.Y, plot.Y)
	require.LessOrEqual(t, line.Y+line.H, plot.Y+plot.H)
	clause, failed, err := s.Validate()
	require.NoError(t, err)
	require.False(t, failed, clause.Message)
}
