package math_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	emmath "github.com/gosuda/elegant-mermaid/internal/math"
)

const bodyPx = 14

func layoutOf(t *testing.T, formula string, sizePx int32) emmath.Box {
	t.Helper()
	box, err := emmath.Layout(mustParse(t, formula), interMetrics{}, sizePx)
	require.NoError(t, err, formula)
	return box
}

func glyphWidth(t *testing.T, weight emmath.Weight, codepoint rune, size int64) int32 {
	t.Helper()
	advance, err := interMetrics{}.Advance(weight, codepoint)
	require.NoError(t, err)
	upem, err := interMetrics{}.Upem(weight)
	require.NoError(t, err)
	return int32(ceilDiv(int64(advance)*size, int64(upem)))
}

func regular(t *testing.T, codepoint rune, size int64) int32 {
	t.Helper()
	return glyphWidth(t, emmath.WeightRegular, codepoint, size)
}

func TestGlyphBox(t *testing.T) {
	box := layoutOf(t, "x", bodyPx)
	width := regular(t, 'x', 896)
	require.Equal(t, emmath.Box{W: width, A: 896, D: 0, Leaves: box.Leaves}, box)
	require.Len(t, box.Leaves, 1)
	leaf := box.Leaves[0]
	require.Equal(t, emmath.LeafGlyph, leaf.Kind)
	require.Equal(t, geom.Rect{X: 0, Y: 0, W: width, H: 896}, leaf.Rect)
	require.Equal(t, 'x', leaf.Codepoint)
	require.Equal(t, emmath.WeightRegular, leaf.Weight)
	require.True(t, leaf.Shear)
	require.Equal(t, int32(896), leaf.Size)
	require.Equal(t, int32(896), leaf.Baseline())
	require.False(t, leaf.Container)
}

func TestTitleSizeScalesTheEm(t *testing.T) {
	box := layoutOf(t, "x", 16)
	require.Equal(t, int32(1024), box.Leaves[0].Size)
	require.Equal(t, int32(1024), box.A)
}

func TestRowWidthSumsGlyphAdvances(t *testing.T) {
	box := layoutOf(t, "x(t)", bodyPx)
	var want int32
	for _, c := range "x(t)" {
		want += regular(t, c, 896)
	}
	require.Equal(t, want, box.W)
	require.Len(t, box.Leaves, 4)
}

func TestFractionGeometry(t *testing.T) {
	box := layoutOf(t, `\frac{1}{1}`, bodyPx)
	digit := regular(t, '1', 896)
	width := digit + 54
	require.Equal(t, width, box.W)
	require.Equal(t, int32(1197), box.A)
	require.Equal(t, int32(748), box.D)
	require.Len(t, box.Leaves, 3)
	require.Equal(t, emmath.Leaf{Kind: emmath.LeafRule, Rect: geom.Rect{X: 0, Y: 950, W: width, H: 45}, Container: true}, box.Leaves[0])
	require.Equal(t, geom.Rect{X: 27, Y: 0, W: digit, H: 896}, box.Leaves[1].Rect)
	require.Equal(t, geom.Rect{X: 27, Y: 1049, W: digit, H: 896}, box.Leaves[2].Rect)
}

func TestScriptPlacement(t *testing.T) {
	box := layoutOf(t, "x^{2}_{i}", bodyPx)
	base := regular(t, 'x', 896)
	sup := regular(t, '2', 627)
	sub := regular(t, 'i', 627)
	require.Len(t, box.Leaves, 3)
	require.Equal(t, geom.Rect{X: 0, Y: 54, W: base, H: 896}, box.Leaves[0].Rect)
	require.Equal(t, geom.Rect{X: base + 27, Y: 0, W: sup, H: 627}, box.Leaves[1].Rect)
	require.Equal(t, geom.Rect{X: base + 27, Y: 627, W: sub, H: 627}, box.Leaves[2].Rect)
	require.Equal(t, int32(627), box.Leaves[1].Size)
	require.Equal(t, base+27+max(sup, sub), box.W)
	require.Equal(t, int32(950), box.A)
	require.Equal(t, int32(304), box.D)
}

func TestSubscriptAloneUsesTheSubShift(t *testing.T) {
	box := layoutOf(t, "x_{i}", bodyPx)
	require.Equal(t, int32(896), box.A)
	require.Equal(t, int32(134), box.D)
	require.Equal(t, int32(896+134-627), box.Leaves[1].Rect.Y)
}

func TestNestedScriptsShrinkAgain(t *testing.T) {
	box := layoutOf(t, "x^{y^{z}}", bodyPx)
	require.Len(t, box.Leaves, 3)
	require.Equal(t, int32(896), box.Leaves[0].Size)
	require.Equal(t, int32(627), box.Leaves[1].Size)
	require.Equal(t, int32(439), box.Leaves[2].Size)
}

func TestBigOperatorLimits(t *testing.T) {
	box := layoutOf(t, `\sum^{n}_{k}`, bodyPx)
	sum := regular(t, '∑', 1254)
	sup := regular(t, 'n', 878)
	sub := regular(t, 'k', 878)
	width := max(sum, sup, sub)
	require.Equal(t, width, box.W)
	require.Equal(t, int32(2222), box.A)
	require.Equal(t, int32(968), box.D)
	require.Len(t, box.Leaves, 3)
	require.Equal(t, int32(1254), box.Leaves[0].Size)
	require.Equal(t, geom.Rect{X: (width - sum) / 2, Y: 968, W: sum, H: 1254}, box.Leaves[0].Rect)
	require.Equal(t, geom.Rect{X: (width - sup) / 2, Y: 0, W: sup, H: 878}, box.Leaves[1].Rect)
	require.Equal(t, geom.Rect{X: (width - sub) / 2, Y: 2312, W: sub, H: 878}, box.Leaves[2].Rect)
}

func TestProductDrawsItsOwnGlyph(t *testing.T) {
	require.Equal(t, '∏', layoutOf(t, `\prod^{n}`, bodyPx).Leaves[0].Codepoint)
	require.Equal(t, '∫', layoutOf(t, `\int^{n}`, bodyPx).Leaves[0].Codepoint)
}

func TestIntegralTakesScriptsToTheRight(t *testing.T) {
	box := layoutOf(t, `\int^{b}_{a}`, bodyPx)
	integral := regular(t, '∫', 1254)
	require.Equal(t, integral+27, box.Leaves[1].Rect.X)
	require.Equal(t, integral+27, box.Leaves[2].Rect.X)
	require.Equal(t, int32(878), box.Leaves[1].Size)
}

func TestLimitPutsAllScriptsBelowInOneRow(t *testing.T) {
	limit := regular(t, 'l', 896) + regular(t, 'i', 896) + regular(t, 'm', 896)
	single := layoutOf(t, `\lim_{n}`, bodyPx)
	script := regular(t, 'n', 627)
	width := max(limit, script)
	require.Equal(t, width, single.W)
	require.Equal(t, int32(896), single.A)
	require.Equal(t, int32(717), single.D)
	require.Len(t, single.Leaves, 4)
	require.Equal(t, geom.Rect{X: (width - script) / 2, Y: 986, W: script, H: 627}, single.Leaves[3].Rect)
	both := layoutOf(t, `\lim^{a}_{b}`, bodyPx)
	first, second := regular(t, 'a', 627), regular(t, 'b', 627)
	row := first + 27 + second
	rowX := (max(limit, row) - row) / 2
	require.Equal(t, rowX, both.Leaves[3].Rect.X)
	require.Equal(t, rowX+first+27, both.Leaves[4].Rect.X)
	require.Equal(t, both.Leaves[3].Rect.Y, both.Leaves[4].Rect.Y)
}

func TestRadicalGeometry(t *testing.T) {
	box := layoutOf(t, `\sqrt{1}`, bodyPx)
	digit := regular(t, '1', 896)
	require.Equal(t, 538+digit, box.W)
	require.Equal(t, int32(950), box.A)
	require.Equal(t, int32(0), box.D)
	require.Len(t, box.Leaves, 3)
	sign := box.Leaves[0]
	require.Equal(t, emmath.LeafPath, sign.Kind)
	require.True(t, sign.Container)
	require.Equal(t, []geom.Point{{X: 0, Y: 380}, {X: 135, Y: 494}, {X: 242, Y: 0}, {X: 538, Y: 0}}, sign.Points)
	require.Equal(t, geom.Rect{X: 0, Y: 0, W: 538, H: 494}, sign.Rect)
	require.Equal(t, emmath.Leaf{Kind: emmath.LeafRule, Rect: geom.Rect{X: 538, Y: 0, W: digit, H: 45}, Container: true}, box.Leaves[1])
	require.Equal(t, geom.Rect{X: 538, Y: 54, W: digit, H: 896}, box.Leaves[2].Rect)
}

func TestRadicalIndexSitsBeforeTheSign(t *testing.T) {
	box := layoutOf(t, `\sqrt[2]{1}`, bodyPx)
	index := regular(t, '2', 627)
	digit := regular(t, '1', 896)
	signX := index + 27
	require.Equal(t, signX+538+digit, box.W)
	require.Len(t, box.Leaves, 4)
	require.Equal(t, signX, box.Leaves[0].Points[0].X)
	require.Equal(t, geom.Rect{X: 0, Y: 0, W: index, H: 627}, box.Leaves[2].Rect)
	require.Equal(t, geom.Rect{X: signX + 538, Y: 54, W: digit, H: 896}, box.Leaves[3].Rect)
	require.Equal(t, int32(950), box.A)
}

func TestDelimitedHeightAndShape(t *testing.T) {
	box := layoutOf(t, `\left(1\right)`, bodyPx)
	digit := regular(t, '1', 896)
	require.Equal(t, 224+digit+224, box.W)
	require.Equal(t, int32(896), box.A)
	require.Equal(t, int32(0), box.D)
	require.Len(t, box.Leaves, 3)
	left := box.Leaves[0]
	require.Equal(t, emmath.LeafPath, left.Kind)
	require.False(t, left.Container)
	require.Len(t, left.Points, 17)
	require.Equal(t, geom.Point{X: 224, Y: 0}, left.Points[0])
	require.Equal(t, geom.Point{X: 112, Y: 448}, left.Points[8])
	require.Equal(t, geom.Point{X: 224, Y: 896}, left.Points[16])
	require.Equal(t, geom.Point{X: 224 + digit, Y: 0}, box.Leaves[2].Points[0])
}

func TestDelimitersGrowAroundShortBodies(t *testing.T) {
	box := layoutOf(t, `\left(\,\right)`, bodyPx)
	require.Equal(t, int32(224+150+224), box.W)
	require.Equal(t, int32(448), box.A)
	require.Equal(t, int32(448), box.D)
	require.Equal(t, int32(0), box.Leaves[0].Rect.Y)
	require.Equal(t, int32(896), box.Leaves[0].Rect.H)
}

func TestDelimiterShapesStayInsideTheirBoxes(t *testing.T) {
	for _, source := range []string{`\left(1\right)`, `\left[1\right]`, `\left\{1\right\}`, `\left|1\right|`, `\left.1\right.`} {
		box := layoutOf(t, source, bodyPx)
		for _, leaf := range box.Leaves {
			inside, err := geom.Contains(box.Bounds(), leaf.Rect)
			require.NoError(t, err, source)
			require.True(t, inside, source)
		}
	}
	require.Len(t, layoutOf(t, `\left.1\right.`, bodyPx).Leaves, 1)
}

func TestSpacingAroundOperators(t *testing.T) {
	a, b := regular(t, 'a', 896), regular(t, 'b', 896)
	equals := regular(t, '=', 896)
	relation := layoutOf(t, "a=b", bodyPx)
	require.Equal(t, a+249, relation.Leaves[1].Rect.X)
	require.Equal(t, a+249+equals+249, relation.Leaves[2].Rect.X)
	require.Equal(t, a+249+equals+249+b, relation.W)
	times := regular(t, '×', 896)
	require.Equal(t, a+199+times+199+b, layoutOf(t, `a\times b`, bodyPx).W)
	require.Equal(t, a+150+b, layoutOf(t, `a\,b`, bodyPx).W)
	require.Equal(t, a+249+b, layoutOf(t, `a\;b`, bodyPx).W)
	require.Equal(t, a+896+b, layoutOf(t, `a\quad b`, bodyPx).W)
}

func TestOperatorSpacingIsOnlyBetweenNeighbours(t *testing.T) {
	a, b := regular(t, 'a', 896), regular(t, 'b', 896)
	equals := regular(t, '=', 896)
	require.Equal(t, a+249+equals, layoutOf(t, "a=", bodyPx).W)
	require.Equal(t, equals+249+b, layoutOf(t, "=b", bodyPx).W)
	require.Equal(t, equals, layoutOf(t, "=", bodyPx).W)
}

func TestScriptedOperatorKeepsItsSpacing(t *testing.T) {
	a, b := regular(t, 'a', 896), regular(t, 'b', 896)
	plusMinus := regular(t, '±', 896)
	scripted := plusMinus + 27 + regular(t, '2', 627)
	require.Equal(t, a+199+scripted+199+b, layoutOf(t, `a\pm^{2}b`, bodyPx).W)
}

func TestFontCommandsSelectWeightAndShear(t *testing.T) {
	bold := layoutOf(t, `\mathbf{x}`, bodyPx)
	require.Equal(t, emmath.WeightBold, bold.Leaves[0].Weight)
	require.False(t, bold.Leaves[0].Shear)
	require.Equal(t, glyphWidth(t, emmath.WeightBold, 'x', 896), bold.W)
	italic := layoutOf(t, `\mathit{1}`, bodyPx)
	require.Equal(t, emmath.WeightRegular, italic.Leaves[0].Weight)
	require.True(t, italic.Leaves[0].Shear)
	require.False(t, layoutOf(t, `\mathrm{x}`, bodyPx).Leaves[0].Shear)
	require.False(t, layoutOf(t, `\alpha`, bodyPx).Leaves[0].Shear)
}

func TestTextModeKeepsSpacesAsGlyphs(t *testing.T) {
	box := layoutOf(t, `\text{a b}`, bodyPx)
	require.Len(t, box.Leaves, 3)
	require.Equal(t, ' ', box.Leaves[1].Codepoint)
	require.False(t, box.Leaves[0].Shear)
}

func TestCdotDrawsTheSubstitutedFontCodepoint(t *testing.T) {
	box := layoutOf(t, `a\cdot b`, bodyPx)
	require.Equal(t, rune(0xB7), box.Leaves[1].Codepoint)
}

func TestLiteralFallbackIsAGlyphRun(t *testing.T) {
	parsed := emmath.Parse("x^{")
	box, err := emmath.Layout(parsed.Expression, interMetrics{}, bodyPx)
	require.NoError(t, err)
	require.Len(t, box.Leaves, 3)
	require.True(t, box.Leaves[0].Shear)
	require.False(t, box.Leaves[1].Shear)
	require.False(t, box.Leaves[2].Shear)
}

func TestLayoutRejectsNegativeSize(t *testing.T) {
	_, err := emmath.Layout(mustParse(t, "x"), interMetrics{}, -1)
	require.ErrorIs(t, err, geom.ErrDomain)
}

func TestLayoutOverflowIsTyped(t *testing.T) {
	_, err := emmath.Layout(mustParse(t, "x"), interMetrics{}, 1<<30)
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func TestLayoutIsDeterministic(t *testing.T) {
	formula := `\sum_{k=1}^{n}\frac{\sqrt[3]{k}}{\left(k+1\right)}`
	require.Equal(t, layoutOf(t, formula, bodyPx), layoutOf(t, formula, bodyPx))
}
