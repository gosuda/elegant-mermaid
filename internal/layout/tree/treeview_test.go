package tree

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var viewMetrics = ViewMetrics{
	RowIndent: 640, PaddingX: 320, PaddingY: 320, TextHeight: 1280,
	IconSize: 896, IconGap: 256, DescGap: 1024, Thickness: 64, Margin: 1024,
}

func viewRows() []ViewRow {
	return []ViewRow{
		{Parent: NoParent, LabelWidth: 100},
		{Parent: 0, LabelWidth: 200},
		{Parent: 1, LabelWidth: 300},
		{Parent: 0, LabelWidth: 50, HasDesc: true, DescWidth: 400},
	}
}

func TestTreeViewPlacesRowsBelowEachOtherAtDepthSteps(t *testing.T) {
	l, err := TreeView(viewRows(), viewMetrics)
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{
		{X: 1024, Y: 1024, W: 740, H: 1920},
		{X: 1984, Y: 2944, W: 840, H: 1920},
		{X: 2944, Y: 4864, W: 940, H: 1920},
		{X: 1984, Y: 6784, W: 690, H: 1920},
	}, l.Boxes)
	require.Equal(t, []int{0, 1, 2, 1}, l.Depth)
	require.Equal(t, geom.Size{W: 6332, H: 9728}, l.Canvas)
}

func TestTreeViewDescriptionsShareOneColumnRightOfTheWidestLabel(t *testing.T) {
	l, err := TreeView(viewRows(), viewMetrics)
	require.NoError(t, err)
	require.Equal(t, int32(4588), l.DescX)
	require.Equal(t, int32(5308), l.Right)
	require.Equal(t, []int32{1344, 2304, 3264, 2304}, l.LabelX)
}

func TestTreeViewRoutesRunDownTheParentSpineThenRight(t *testing.T) {
	l, err := TreeView(viewRows(), viewMetrics)
	require.NoError(t, err)
	require.Nil(t, l.Routes[0])
	require.Equal(t, []geom.Point{{X: 1344, Y: 2944}, {X: 1344, Y: 3904}, {X: 1984, Y: 3904}}, l.Routes[1])
	require.Equal(t, []geom.Point{{X: 2304, Y: 4864}, {X: 2304, Y: 5824}, {X: 2944, Y: 5824}}, l.Routes[2])
	require.Equal(t, []geom.Point{{X: 1344, Y: 2944}, {X: 1344, Y: 7744}, {X: 1984, Y: 7744}}, l.Routes[3])
}

func TestTreeViewIconShiftsLabelAndWidensBox(t *testing.T) {
	rows := viewRows()
	rows[1].HasIcon = true
	l, err := TreeView(rows, viewMetrics)
	require.NoError(t, err)
	require.Equal(t, int32(2304+896+256), l.LabelX[1])
	require.Equal(t, int32(840+896+256), l.Boxes[1].W)
	require.Equal(t, int32(2304), l.IconX[1])
}

func TestTreeViewDropsFirstRoutePointWhenSpineEndsAtTheRowMiddle(t *testing.T) {
	m := viewMetrics
	m.TextHeight, m.PaddingY = 1, 0
	l, err := TreeView(viewRows()[:2], m)
	require.NoError(t, err)
	require.Len(t, l.Routes[1], 2)
	require.Equal(t, l.Routes[1][0].Y, l.Routes[1][1].Y)
}

func TestTreeViewRejectsBrokenInput(t *testing.T) {
	for name, tc := range map[string]struct {
		rows []ViewRow
		m    ViewMetrics
	}{
		"empty":           {nil, viewMetrics},
		"rooted child":    {[]ViewRow{{Parent: 0}}, viewMetrics},
		"forward parent":  {[]ViewRow{{Parent: NoParent}, {Parent: 2}, {Parent: 0}}, viewMetrics},
		"self parent":     {[]ViewRow{{Parent: NoParent}, {Parent: 1}}, viewMetrics},
		"negative width":  {[]ViewRow{{Parent: NoParent}, {Parent: 0, LabelWidth: -1}}, viewMetrics},
		"no text height":  {viewRows(), ViewMetrics{}},
		"negative indent": {viewRows(), ViewMetrics{TextHeight: 1, RowIndent: -1}},
	} {
		_, err := TreeView(tc.rows, tc.m)
		require.ErrorIs(t, err, ErrInvalid, name)
	}
}

func TestTreeViewReportsOverflow(t *testing.T) {
	rows := []ViewRow{{Parent: NoParent, LabelWidth: 1 << 29}}
	_, err := TreeView(rows, viewMetrics)
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func TestTreePrefixesMarkLastChildAndKeepTrunks(t *testing.T) {
	rows := []ViewRow{{Parent: NoParent}, {Parent: 0}, {Parent: 1}, {Parent: 1}, {Parent: 0}, {Parent: 4}}
	require.Equal(t, []string{
		"", "├── ", "│   ├── ", "│   └── ", "└── ", "    └── ",
	}, TreePrefixes(rows))
}

func TestTreePrefixesOfEmptyInput(t *testing.T) {
	require.Empty(t, TreePrefixes(nil))
}
