package cells

import (
	"math"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/stretchr/testify/require"
)

func TestPositionedLinesUseAlignedCellWidths(t *testing.T) {
	cases := []struct {
		name  string
		align scene.Align
		text  string
		x     int32
		width int32
	}{
		{"start", scene.AlignStart, "ab", 10, 2},
		{"middle", scene.AlignMiddle, "ab", 11, 2},
		{"end", scene.AlignEnd, "ab", 13, 2},
		{"negative-middle-gap", scene.AlignMiddle, "abcdef", 9, 6},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			item := &scene.Text{
				Rect: geom.Rect{X: 10, Y: 5, W: 5, H: 1}, Align: tc.align,
				Lines: [][]scene.Run{{{Text: tc.text}}},
			}
			lines, err := PositionedLines(item)
			require.NoError(t, err)
			require.Equal(t, []PositionedLine{{
				Text: tc.text, Rect: geom.Rect{X: tc.x, Y: 5, W: tc.width, H: 1},
			}}, lines)
		})
	}
}

func TestPositionedLinesNormalizeBeforeMeasuringWithoutHeightClipping(t *testing.T) {
	item := &scene.Text{
		Rect: geom.Rect{X: 10, Y: 5, W: 6}, Align: scene.AlignMiddle,
		Lines: [][]scene.Run{
			{{Text: "A"}, {Text: "\u0301"}},
			{{Text: "\x1b"}, {Text: "\u0301B"}},
			{},
			{{Text: " "}},
			{{Text: "👩"}, {Text: "\u200d"}, {Text: "🔬"}},
		},
	}
	lines, err := PositionedLines(item)
	require.NoError(t, err)
	require.Equal(t, []PositionedLine{
		{Text: "A\u0301", Rect: geom.Rect{X: 12, Y: 5, W: 1, H: 1}},
		{Text: "\ufffd\u0301B", Rect: geom.Rect{X: 12, Y: 6, W: 2, H: 1}},
		{Text: "", Rect: geom.Rect{X: 13, Y: 7, H: 1}},
		{Text: " ", Rect: geom.Rect{X: 12, Y: 8, W: 1, H: 1}},
		{Text: "👩\u200d🔬", Rect: geom.Rect{X: 12, Y: 9, W: 2, H: 1}},
	}, lines)
}

func TestPositionedLinesRejectCoordinateOverflow(t *testing.T) {
	for _, item := range []*scene.Text{
		{Rect: geom.Rect{X: math.MaxInt32, W: 2}, Align: scene.AlignEnd, Lines: [][]scene.Run{{{Text: "X"}}}},
		{Rect: geom.Rect{Y: math.MaxInt32, W: 1}, Lines: [][]scene.Run{{{Text: "X"}}, {{Text: "Y"}}}},
	} {
		lines, err := PositionedLines(item)
		require.ErrorIs(t, err, geom.ErrOverflow)
		require.Nil(t, lines)
	}
}
