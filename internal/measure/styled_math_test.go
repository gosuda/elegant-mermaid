package measure

import (
	"math"
	"testing"

	"github.com/stretchr/testify/require"

	emath "github.com/gosuda/elegant-mermaid/internal/math"
)

func formulaWidthAt(t *testing.T, formula string, sizePx int32) int32 {
	t.Helper()
	parsed := emath.Parse(formula)
	require.Empty(t, parsed.Diagnostics, formula)
	box, err := emath.Layout(parsed.Expression, formulaMetrics{}, sizePx)
	require.NoError(t, err)
	return box.W
}

func TestVectorMathSpanIsOneAtomicRun(t *testing.T) {
	metric := ForRole(RoleLabel)
	lines, err := StyledLines("$$x(t)$$", math.MaxInt32, metric)
	require.NoError(t, err)
	require.Len(t, lines, 1)
	want := formulaWidthAt(t, "x(t)", 14)
	require.Equal(t, "$$x(t)$$", lines[0].Text)
	require.Equal(t, want, lines[0].Width)
	require.Len(t, lines[0].Runs, 1)
	run := lines[0].Runs[0]
	require.Equal(t, "$$x(t)$$", run.Text)
	require.Equal(t, want, run.Width)
	require.NotNil(t, run.Math)
	require.Equal(t, want, run.Math.W)
	require.False(t, run.Bold)
	require.False(t, run.Italic)
}

func TestInvalidFormulaStaysLiteralText(t *testing.T) {
	metric := ForRole(RoleLabel)
	lines, err := StyledLines(`$$\foo$$`, math.MaxInt32, metric)
	require.NoError(t, err)
	require.Len(t, lines, 1)
	require.Equal(t, `$$\foo$$`, lines[0].Text)
	require.Len(t, lines[0].Runs, 1)
	require.Nil(t, lines[0].Runs[0].Math)
	literal, err := metric.TextWidth(`$$\foo$$`)
	require.NoError(t, err)
	require.Equal(t, literal, lines[0].Width)
}

func TestCellProfileKeepsMathAsLiteralText(t *testing.T) {
	lines, err := StyledLines("a $$x$$", math.MaxInt32, CellMetric())
	require.NoError(t, err)
	require.Len(t, lines, 1)
	require.Equal(t, "a $$x$$", lines[0].Text)
	require.Equal(t, int32(7), lines[0].Width)
	for _, run := range lines[0].Runs {
		require.Nil(t, run.Math)
	}
}

func TestFontFamilyFactorCoversTheWholeLine(t *testing.T) {
	metric := ForRole(RoleLabel)
	metric.FontFamily = true
	lines, err := StyledLines("$$x(t)$$", math.MaxInt32, metric)
	require.NoError(t, err)
	box := formulaWidthAt(t, "x(t)", 14)
	require.Equal(t, box*108/100, lines[0].Width)
	require.Equal(t, box, lines[0].Runs[0].Width)
}

func TestMathSpanWidthJoinsSurroundingText(t *testing.T) {
	metric := ForRole(RoleLabel)
	lines, err := StyledLines("ab $$x$$ cd", math.MaxInt32, metric)
	require.NoError(t, err)
	require.Len(t, lines, 1)
	require.Equal(t, "ab $$x$$ cd", lines[0].Text)
	require.Len(t, lines[0].Runs, 3)
	require.Nil(t, lines[0].Runs[0].Math)
	require.NotNil(t, lines[0].Runs[1].Math)
	require.Nil(t, lines[0].Runs[2].Math)
	text, err := metric.TextWidth("ab ")
	require.NoError(t, err)
	tail, err := metric.TextWidth(" cd")
	require.NoError(t, err)
	require.Equal(t, text+lines[0].Runs[1].Width+tail, lines[0].Width)
}

func TestWrappingNeverSplitsAFormula(t *testing.T) {
	lines, err := StyledLines("a $$b c$$ d", 1, ForRole(RoleLabel))
	require.NoError(t, err)
	var texts []string
	for _, line := range lines {
		texts = append(texts, line.Text)
	}
	require.Equal(t, []string{"a", "$$b c$$", "d"}, texts)
}

func TestMathInsideEmphasisIsNotStyled(t *testing.T) {
	lines, err := StyledLines("**a $$x$$**", math.MaxInt32, ForRole(RoleLabel))
	require.NoError(t, err)
	require.Len(t, lines, 1)
	require.Equal(t, "a $$x$$", lines[0].Text)
	require.Len(t, lines[0].Runs, 2)
	require.True(t, lines[0].Runs[0].Bold)
	require.NotNil(t, lines[0].Runs[1].Math)
	require.False(t, lines[0].Runs[1].Bold)
}

func TestEmptyFormulaHasNoWidth(t *testing.T) {
	lines, err := StyledLines("$$$$", math.MaxInt32, ForRole(RoleLabel))
	require.NoError(t, err)
	require.Len(t, lines, 1)
	require.Equal(t, "$$$$", lines[0].Text)
	require.Equal(t, int32(0), lines[0].Width)
	require.NotNil(t, lines[0].Runs[0].Math)
}

func TestFormulaSizeFollowsTheMetric(t *testing.T) {
	title, err := StyledLines("$$x$$", math.MaxInt32, ForRole(RoleTitle))
	require.NoError(t, err)
	require.Equal(t, formulaWidthAt(t, "x", 16), title[0].Width)
}

func TestEscapedDollarsInsideAFormula(t *testing.T) {
	lines, err := StyledLines(`$$a\$b$$`, math.MaxInt32, ForRole(RoleLabel))
	require.NoError(t, err)
	require.Len(t, lines[0].Runs, 1)
	require.NotNil(t, lines[0].Runs[0].Math)
	require.Equal(t, `$$a\$b$$`, lines[0].Text)
}

func TestMathOverflowIsTyped(t *testing.T) {
	metric := Metric{Profile: ProfileVector, SizePx: 1 << 30, Weight: WeightRegular}
	_, err := StyledLines("$$x$$", math.MaxInt32, metric)
	require.Error(t, err)
}
