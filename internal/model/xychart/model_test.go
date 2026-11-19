package xychart_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	model "github.com/gosuda/elegant-mermaid/internal/model/xychart"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/xychart"
)

func resolve(t *testing.T, text string) *model.Model {
	t.Helper()
	start, ds := parser.Parse([]byte(text), syntax.Preprocess([]byte(text)).Removed)
	require.Empty(t, ds)
	m, rs := model.Resolve([]byte(text), start)
	require.Empty(t, rs)
	return m
}

func TestThousandthsRoundsHalfAwayFromZero(t *testing.T) {
	for literal, want := range map[string]int64{
		"1": 1000, "0.0005": 1, "0.0004": 0, "-0.0005": -1, "2.5": 2500, "-2.5": -2500, ".5": 500, "+3": 3000,
		"0.1239": 124, "10": 10000, "007": 7000,
	} {
		require.Equal(t, want, model.Thousandths(literal), literal)
	}
}

func TestThousandthsCapsHugeValuesAboveInt32(t *testing.T) {
	require.Greater(t, model.Thousandths("99999999999999999999999"), int64(1<<31-1))
	require.Less(t, model.Thousandths("-99999999999999999999999"), -int64(1<<31-1))
}

func TestFirstPlotWithoutXAxisFixesALinearDomain(t *testing.T) {
	m := resolve(t, "xychart\nbar [3, 1, 2]\nline [9, 9, 9, 9, 9]\n")
	require.False(t, m.X.Band)
	require.Equal(t, int64(1000), m.X.Min)
	require.Equal(t, int64(3000), m.X.Max)
	require.Equal(t, int64(1000), m.Y.Min)
	require.Equal(t, int64(9000), m.Y.Max)
	require.Len(t, m.Plots[1].Points, 5)
	require.Equal(t, int64(1000), m.Plots[0].Points[0].X)
	require.Equal(t, int64(2000), m.Plots[0].Points[1].X)
	require.Equal(t, int64(3000), m.Plots[0].Points[2].X)
}

func TestLinearAxisSpreadsPointsEvenly(t *testing.T) {
	m := resolve(t, "xychart\nx-axis 0 --> 10\nline [1, 2, 3]\n")
	var xs []int64
	for _, p := range m.Plots[0].Points {
		require.True(t, p.HasX)
		xs = append(xs, p.X)
	}
	require.Equal(t, []int64{0, 5000, 10000}, xs)
}

func TestSingleValueSitsAtTheDomainMinimum(t *testing.T) {
	m := resolve(t, "xychart\nx-axis 4 --> 8\nline [1]\n")
	require.Equal(t, int64(4000), m.Plots[0].Points[0].X)
}

func TestBandPlotTruncatesExcessAndKeepsMissingValuesAbsent(t *testing.T) {
	m := resolve(t, "xychart\nx-axis [a, b, c]\nbar [1, 2, 3, 40]\nbar [5]\n")
	require.Equal(t, int64(5000), m.Y.Max)
	require.Len(t, m.Plots[0].Points, 3)
	short := m.Plots[1].Points
	require.Len(t, short, 3)
	require.True(t, short[0].Present)
	require.False(t, short[1].Present)
	require.False(t, short[2].Present)
	require.Equal(t, int64(1000), m.Y.Min)
}

func TestExplicitYRangeStopsInference(t *testing.T) {
	m := resolve(t, "xychart\nx-axis [a]\nbar [100]\ny-axis 0 --> 10\nbar [200]\n")
	require.Equal(t, int64(0), m.Y.Min)
	require.Equal(t, int64(10000), m.Y.Max)
}

func TestTitleOnlyAxisKeepsInference(t *testing.T) {
	m := resolve(t, "xychart\nx-axis \"Months\"\ny-axis Units\nbar [4, 8]\n")
	require.Equal(t, "Months", m.X.Title)
	require.Equal(t, "Units", m.Y.Title)
	require.Equal(t, int64(4000), m.Y.Min)
	require.Equal(t, int64(8000), m.Y.Max)
	require.False(t, m.X.Band)
}

func TestAxisDataWithoutTitleClearsTheTitle(t *testing.T) {
	m := resolve(t, "xychart\nx-axis Months\nx-axis [a, b]\n")
	require.Equal(t, "", m.X.Title)
	require.True(t, m.X.Band)
}

func TestDuplicateCategoriesUseTheFirstSlot(t *testing.T) {
	m := resolve(t, "xychart\nx-axis [a, b, a]\nbar [1, 2, 3]\n")
	require.Equal(t, []int{0, 1, 0}, []int{m.Plots[0].Points[0].Slot, m.Plots[0].Points[1].Slot, m.Plots[0].Points[2].Slot})
}

func TestRedefinedAxisLeavesEarlierPlotsUnplaced(t *testing.T) {
	m := resolve(t, "xychart\nx-axis [a, b]\nbar [1, 2]\nx-axis 0 --> 5\n")
	for _, p := range m.Plots[0].Points {
		require.Equal(t, model.NoSlot, p.Slot)
		require.False(t, p.HasX)
	}
}

func TestOnlyLinePlotsKeepPointLabels(t *testing.T) {
	m := resolve(t, "xychart\nx-axis [a, b]\nline [1 \"x\", 2]\nbar [1 \"y\", 2]\n")
	require.Equal(t, "x", m.Plots[0].Points[0].Label)
	require.Equal(t, "", m.Plots[1].Points[0].Label)
}

func TestHeaderOrientationOverridesConfig(t *testing.T) {
	m := resolve(t, "---\nconfig:\n  xyChart:\n    chartOrientation: horizontal\n---\nxychart\nbar [1]\n")
	require.Equal(t, model.Horizontal, m.Orientation)
	m = resolve(t, "---\nconfig:\n  xyChart:\n    chartOrientation: horizontal\n---\nxychart vertical\nbar [1]\n")
	require.Equal(t, model.Vertical, m.Orientation)
	m = resolve(t, "xychart HORIZONTAL\nbar [1]\n")
	require.Equal(t, model.Vertical, m.Orientation)
}

func TestTitlesAndAccessibilityAreTrimmedAndReplaced(t *testing.T) {
	m := resolve(t, "xychart\ntitle \"  First  \"\ntitle Second\naccTitle:  T1 \naccDescr: D1\naccDescr {\n D2 \n}\nbar [1]\n")
	require.Equal(t, "Second", m.Title)
	require.Equal(t, "T1", m.AccTitle)
	require.Equal(t, "D2", m.AccDescr)
}

func TestFrontmatterTitleIsTheDiagramTitle(t *testing.T) {
	m := resolve(t, "---\ntitle: From front\n---\nxychart\nbar [1]\n")
	require.Equal(t, "From front", m.Title)
}

func TestHonouredConfigKeysAreKeptSortedAndRangeChecked(t *testing.T) {
	m := resolve(t, "---\nconfig:\n  xyChart:\n    width: 900\n    height: 0\n    unknownKey: 0\n    plotReservedSpacePercent: 60\n    showTitle: false\n    xAxis:\n      showLabel: false\n      labelFontSize: 20\n---\nxychart\nbar [1]\n")
	var keys []string
	for _, e := range m.Config {
		keys = append(keys, e.Key)
	}
	require.Equal(t, []string{"plotReservedSpacePercent", "width", "xAxis.labelFontSize", "xAxis.showLabel"}, keys)
}

func TestEntitiesDecodeInText(t *testing.T) {
	m := resolve(t, "xychart\ntitle \"a #35; b #amp; c\"\nbar [1]\n")
	require.Equal(t, "a # b & c", m.Title)
}
