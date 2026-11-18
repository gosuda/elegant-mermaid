package math_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	emmath "github.com/gosuda/elegant-mermaid/internal/math"
)

func forms(t *testing.T, formula, unicode, ascii string) {
	t.Helper()
	parsed := emmath.Parse(formula)
	require.Equal(t, unicode, emmath.Linear(parsed.Expression, emmath.CharsetUnicode), "unicode linear form of %q", formula)
	require.Equal(t, ascii, emmath.Linear(parsed.Expression, emmath.CharsetASCII), "ascii linear form of %q", formula)
}

func TestConstructTableForms(t *testing.T) {
	forms(t, "x", "x", "x")
	forms(t, "{xy}", "xy", "xy")
	forms(t, "a,b", "a,b", "a,b")
	forms(t, `\frac{a}{b}`, "(a)/(b)", "(a)/(b)")
	forms(t, `\sqrt{x}`, "√(x)", "sqrt(x)")
	forms(t, `\sqrt[3]{x}`, "³√(x)", "[3]sqrt(x)")
	forms(t, `\sum^{n}_{k}x`, "∑ⁿₖx", "sum^(n)_(k)x")
	forms(t, `\prod`, "∏", "prod")
	forms(t, `\int`, "∫", "int")
	forms(t, `\lim`, "lim", "lim")
	forms(t, `\lim_{x\to 0}`, "lim_(x→0)", "lim_(x->0)")
	forms(t, `\infty`, "∞", "inf")
	forms(t, `\alpha`, "α", "alpha")
	forms(t, `\Gamma`, "Γ", "Gamma")
	forms(t, `\pm\times\div\cdot`, "±×÷⋅", "+-x/.")
	forms(t, "=", "=", "=")
	forms(t, `\le\ge\ne\approx\to\leftarrow\Rightarrow\Leftrightarrow`, "≤≥≠≈→←⇒⇔", "<=>=!=~=-><-=><=>")
	forms(t, `\left(x\right)`, "(x)", "(x)")
	forms(t, `\left|x\right|`, "|x|", "|x|")
	forms(t, `\left\{x\right\}`, "{x}", "{x}")
	forms(t, `\left.x\right.`, "x", "x")
	forms(t, `\mathbf{x}\mathit{y}\mathrm{z}\text{w}`, "xyzw", "xyzw")
	forms(t, `a\,b`, "ab", "ab")
	forms(t, `a\;b`, "a b", "a b")
	forms(t, `a\quad b`, "a  b", "a  b")
}

func TestScriptsConvertInUnicodeAndStayBracketedInASCII(t *testing.T) {
	forms(t, "x^{12}", "x¹²", "x^(12)")
	forms(t, "x_n", "xₙ", "x_(n)")
	forms(t, `\sqrt[2]{x}`, "²√(x)", "[2]sqrt(x)")
}

func TestMixedScriptsStayWhollyParenthesised(t *testing.T) {
	forms(t, "x^{min}", "x^(min)", "x^(min)")
	forms(t, "x_{ba}", "x_(ba)", "x_(ba)")
	forms(t, "x^{min}_{a}", "x^(min)ₐ", "x^(min)_(a)")
	forms(t, "x^{2}_{ba}", "x²_(ba)", "x^(2)_(ba)")
}

func TestEmptyScriptConvertsToNothing(t *testing.T) {
	forms(t, "x^{}", "x", "x^()")
	forms(t, "x^{}_{a}", "xₐ", "x^()_(a)")
}

func TestNestedConstructsKeepTheirDelimiters(t *testing.T) {
	forms(t, `\frac{\sqrt{x}}{a+b}`, "(√(x))/(a+b)", "(sqrt(x))/(a+b)")
	forms(t, `\sqrt{\frac{a}{b}}`, "√((a)/(b))", "sqrt((a)/(b))")
	forms(t, `\sqrt[\frac{1}{2}]{x}`, "[(1)/(2)]√(x)", "[(1)/(2)]sqrt(x)")
}

func TestFailedFormulaPrintsTheExactSource(t *testing.T) {
	truncated := emmath.Parse("x^{")
	require.Len(t, truncated.Diagnostics, 1)
	require.Equal(t, "x^{", emmath.Linear(truncated.Expression, emmath.CharsetUnicode))
	require.Equal(t, "x^{", emmath.Linear(truncated.Expression, emmath.CharsetASCII))
	unsupported := emmath.Parse(`a\foo{b}`)
	require.Len(t, unsupported.Diagnostics, 1)
	require.Equal(t, `a\foo{b}`, emmath.Linear(unsupported.Expression, emmath.CharsetASCII))
}

func TestCdotStaysLogicalInTheUnicodeCell(t *testing.T) {
	parsed := emmath.Parse(`a\cdot b`)
	require.Empty(t, parsed.Diagnostics)
	unicode := emmath.Linear(parsed.Expression, emmath.CharsetUnicode)
	require.Equal(t, "a\u22C5b", unicode)
	require.NotContains(t, unicode, "\u00B7")
	require.Equal(t, "a.b", emmath.Linear(parsed.Expression, emmath.CharsetASCII))
}
