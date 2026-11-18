package math_test

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	emmath "github.com/gosuda/elegant-mermaid/internal/math"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func rowOf(t *testing.T, e *emmath.Expr) []*emmath.Expr {
	t.Helper()
	require.Equal(t, emmath.KindRow, e.Kind, "expected horizontal concatenation")
	return e.Children
}

func mustParse(t *testing.T, formula string) *emmath.Expr {
	t.Helper()
	parsed := emmath.Parse(formula)
	require.Empty(t, parsed.Diagnostics, formula)
	return parsed.Expression
}

func TestDefaultFontsAndGreekAreDistinct(t *testing.T) {
	children := rowOf(t, mustParse(t, "x2α\\alpha=\\infty"))
	require.Equal(t, emmath.KindGlyph, children[0].Kind)
	require.Equal(t, 'x', children[0].Char)
	require.Equal(t, emmath.FontItalic, children[0].Font)
	require.Equal(t, '2', children[1].Char)
	require.Equal(t, emmath.FontRoman, children[1].Font)
	require.Equal(t, 'α', children[2].Char)
	require.Equal(t, emmath.FontRoman, children[2].Font)
	require.Equal(t, emmath.KindSymbol, children[3].Kind)
	require.Equal(t, "alpha", children[3].Command)
	require.Equal(t, 'α', children[3].Char)
	require.Equal(t, emmath.ClassGreek, children[3].Class)
	require.Equal(t, emmath.FontRoman, children[3].Font)
	require.Equal(t, emmath.ClassRelation, children[4].Class)
	require.Equal(t, source.Span{Start: 4, End: 10}, children[3].Span)
}

func TestScriptsBindToOneAtomOrGroup(t *testing.T) {
	children := rowOf(t, mustParse(t, `ab^23_{ij}+\frac{x}{y}`))
	require.Equal(t, 'a', children[0].Char)
	require.Equal(t, emmath.KindScripts, children[1].Kind)
	require.Equal(t, 'b', children[1].Base.Char)
	require.Equal(t, '2', children[1].Superscript.Char)
	require.Nil(t, children[1].Subscript)
	require.Equal(t, emmath.KindScripts, children[2].Kind)
	require.Equal(t, '3', children[2].Base.Char)
	require.Equal(t, emmath.KindGroup, children[2].Subscript.Kind)
	require.Equal(t, emmath.KindFraction, children[4].Kind)
	paired := rowOf(t, mustParse(t, "x_{1}^{2}"))
	require.NotNil(t, paired[0].Superscript)
	require.NotNil(t, paired[0].Subscript)
}

func TestRadicalsPreserveOptionalIndex(t *testing.T) {
	for source, indexed := range map[string]bool{`\sqrt{x}`: false, `\sqrt[n+1]{x}`: true} {
		radical := rowOf(t, mustParse(t, source))[0]
		require.Equal(t, emmath.KindRadical, radical.Kind, source)
		require.Equal(t, indexed, radical.Index != nil, source)
		require.Equal(t, emmath.KindGroup, radical.Radicand.Kind, source)
	}
}

func TestExplicitFontsAndTextKeepSemantics(t *testing.T) {
	for source, want := range map[string]emmath.Font{
		`\mathbf{x1}`: emmath.FontBold,
		`\mathit{x1}`: emmath.FontItalic,
		`\mathrm{x1}`: emmath.FontRoman,
	} {
		styled := rowOf(t, mustParse(t, source))[0]
		require.Equal(t, emmath.KindStyled, styled.Kind, source)
		require.Equal(t, want, styled.Font, source)
		require.Equal(t, emmath.KindGroup, styled.Body.Kind, source)
		for _, item := range rowOf(t, styled.Body.Body) {
			require.Equal(t, want, item.Font, source)
		}
	}
	text := rowOf(t, mustParse(t, `\text{a b_^\$}`))[0]
	require.Equal(t, emmath.KindText, text.Kind)
	content := rowOf(t, text.Body.Body)
	require.Len(t, content, 6)
	for _, item := range content {
		require.Equal(t, emmath.KindGlyph, item.Kind)
		require.Equal(t, emmath.FontRoman, item.Font)
	}
}

func TestEveryDelimiterShapeIsTyped(t *testing.T) {
	cases := []struct {
		left, right string
		l, r        emmath.Delimiter
	}{
		{"(", ")", emmath.DelimLeftParen, emmath.DelimRightParen},
		{"[", "]", emmath.DelimLeftBracket, emmath.DelimRightBracket},
		{`\{`, `\}`, emmath.DelimLeftBrace, emmath.DelimRightBrace},
		{"|", "|", emmath.DelimBar, emmath.DelimBar},
		{".", ".", emmath.DelimInvisible, emmath.DelimInvisible},
	}
	for _, c := range cases {
		source := `\left` + c.left + `x\right` + c.right
		delimited := rowOf(t, mustParse(t, source))[0]
		require.Equal(t, emmath.KindDelimited, delimited.Kind, source)
		require.Equal(t, c.l, delimited.Left, source)
		require.Equal(t, c.r, delimited.Right, source)
	}
}

func TestClosedSymbolsAreRetained(t *testing.T) {
	children := rowOf(t, mustParse(t, `\sum\prod\int\lim\pm\times\div\cdot\le\ge\ne\approx\to\leftarrow\Rightarrow\Leftrightarrow`))
	require.Len(t, children, 16)
	require.Equal(t, emmath.ClassSum, children[0].Class)
	require.Equal(t, emmath.ClassProduct, children[1].Class)
	require.Equal(t, emmath.ClassIntegral, children[2].Class)
	require.Equal(t, emmath.KindLimit, children[3].Kind)
	require.Equal(t, emmath.FontRoman, children[3].Font)
	for _, node := range children[4:8] {
		require.Equal(t, emmath.ClassBinary, node.Class)
	}
	for _, node := range children[8:16] {
		require.Equal(t, emmath.ClassRelation, node.Class)
	}
}

func TestFixedSpacesAreRetained(t *testing.T) {
	children := rowOf(t, mustParse(t, `\,\;\quad`))
	require.Equal(t, emmath.SpaceThin, children[0].Space)
	require.Equal(t, emmath.SpaceMedium, children[1].Space)
	require.Equal(t, emmath.SpaceQuad, children[2].Space)
}

func TestEscapesAndEntitiesAreNotReinterpreted(t *testing.T) {
	children := rowOf(t, mustParse(t, `\$\{\}\_\^\\#alpha;`))
	var characters strings.Builder
	for _, node := range children {
		require.Equal(t, emmath.KindGlyph, node.Kind)
		characters.WriteRune(node.Char)
	}
	require.Equal(t, `${}_^\#alpha;`, characters.String())
}

func TestUnsupportedCommandsFallBackToEntireSource(t *testing.T) {
	for _, command := range []string{"unknown", "omicron", "varpi", "varrho", "varsigma", "alphabeta"} {
		formula := `α+\` + command + `+x`
		parsed := emmath.Parse(formula)
		require.Equal(t, emmath.KindLiteral, parsed.Expression.Kind, formula)
		require.Equal(t, formula, parsed.Expression.Literal, formula)
		require.Len(t, parsed.Diagnostics, 1, formula)
		d := parsed.Diagnostics[0]
		require.Equal(t, "math/unsupported-command", d.Code)
		require.Equal(t, diag.SeverityWarning, d.Severity)
		require.Equal(t, `unsupported math command \`+command, d.Message)
		require.Equal(t, "The source text is shown as written.", d.Help)
		require.Equal(t, source.Span{Start: 0, End: len(formula)}, d.Span)
	}
}

func TestMalformedConstructsReportWholeFormulaSpan(t *testing.T) {
	for _, formula := range []string{
		"{x", "x}", `\frac{x}`, `\frac x{y}`, `\sqrt`, `\sqrt[2{x}`, "x^", "x_", "^x", "x^1^2",
		`\left(x`, `\right)`, `\left x\right)`, "\\",
	} {
		parsed := emmath.Parse(formula)
		require.Equal(t, emmath.KindLiteral, parsed.Expression.Kind, formula)
		require.Equal(t, formula, parsed.Expression.Literal, formula)
		require.NotEmpty(t, parsed.Diagnostics, formula)
		d := parsed.Diagnostics[0]
		require.Equal(t, "math/syntax", d.Code, formula)
		require.Equal(t, diag.SeverityError, d.Severity, formula)
		require.True(t, strings.HasPrefix(d.Message, "invalid math syntax: "), formula)
		require.Equal(t, source.Span{Start: 0, End: len(formula)}, d.Span, formula)
		require.Equal(t, "The source text is shown as written.", d.Help, formula)
	}
}

func TestNestingLimitIsNotASilentCap(t *testing.T) {
	accepted := strings.Repeat("{", 64) + "x" + strings.Repeat("}", 64)
	require.Empty(t, emmath.Parse(accepted).Diagnostics)
	parsed := emmath.Parse("{" + accepted + "}")
	require.NotEmpty(t, parsed.Diagnostics)
	require.Equal(t, "limit/nesting-depth", parsed.Diagnostics[0].Code)
	require.Equal(t, source.Span{Start: 64, End: 65}, parsed.Diagnostics[0].Span)
}

func TestNestingLimitSpanCoversWholeScalar(t *testing.T) {
	formula := strings.Repeat("{", 64) + "é"
	parsed := emmath.Parse("{" + formula)
	require.NotEmpty(t, parsed.Diagnostics)
	require.Equal(t, "limit/nesting-depth", parsed.Diagnostics[0].Code)
	require.Equal(t, source.Span{Start: 64, End: 65}, parsed.Diagnostics[0].Span)
}

func TestEveryNormativeGreekNameIsSupportedUpright(t *testing.T) {
	names := strings.Fields("alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa lambda mu nu xi pi rho sigma tau upsilon phi varphi chi psi omega Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega")
	require.Len(t, names, 37)
	for _, name := range names {
		symbol := rowOf(t, mustParse(t, `\`+name))[0]
		require.Equal(t, emmath.KindSymbol, symbol.Kind, name)
		require.Equal(t, emmath.ClassGreek, symbol.Class, name)
		require.Equal(t, emmath.FontRoman, symbol.Font, name)
	}
}

func TestInvalidUTF8IsNeverFatal(t *testing.T) {
	for _, formula := range []string{"\xff", "x^\xff", "\\\xff", "\\frac{\xc3}{\xe2\x82}", "{" + strings.Repeat("{", 63) + "\xff"} {
		parsed := emmath.Parse(formula)
		require.NotNil(t, parsed.Expression, fmt.Sprintf("%q", formula))
	}
}
