package xychart_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/xychart"
)

func parse(t *testing.T, text string) (*parser.Start, []diag.Diagnostic) {
	t.Helper()
	removed := syntax.Preprocess([]byte(text)).Removed
	return parser.Parse([]byte(text), removed)
}

func TestFullChartStatements(t *testing.T) {
	src := "xychart-beta horizontal\n  title \"Sales\"\n  x-axis Months [jan, \"feb x\", mar]\n  y-axis \"Revenue\" 0 --> 10.5\n  bar [1, 2.5, -3]\n  line \"L\" [3 \"p\", 4]\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	require.Len(t, start.Headers, 1)
	require.Equal(t, "horizontal", start.Headers[0].Orientation.Text)
	kinds := start.Document.Statements
	require.Len(t, kinds, 5)
	require.Equal(t, "Sales", kinds[0].Kind.(*parser.Title).Text.Value)
	x := kinds[1].Kind.(*parser.AxisStatement)
	require.False(t, x.Y)
	require.Equal(t, "Months", x.Title.Value)
	require.Len(t, x.Band.Categories, 3)
	require.Equal(t, "feb x", x.Band.Categories[1].Value)
	y := kinds[2].Kind.(*parser.AxisStatement)
	require.True(t, y.Y)
	require.Equal(t, "10.5", y.Range.Max.Text)
	bar := kinds[3].Kind.(*parser.PlotStatement)
	require.False(t, bar.Line)
	require.Nil(t, bar.Title)
	require.Equal(t, "-3", bar.Data.Points[2].Number.Text)
	line := kinds[4].Kind.(*parser.PlotStatement)
	require.True(t, line.Line)
	require.Equal(t, "L", line.Title.Value)
	require.Equal(t, "p", line.Data.Points[0].Label.Value)
	require.Nil(t, line.Data.Points[1].Label)
}

func TestSemicolonSeparatesStatementsOnOneLine(t *testing.T) {
	start, ds := parse(t, "xychart\ntitle T; x-axis [a, b]; bar [1, 2]\n")
	require.Empty(t, ds)
	require.Len(t, start.Document.Statements, 3)
}

func TestUnquotedTextConcatenatesTokensWithoutSpaces(t *testing.T) {
	start, ds := parse(t, "xychart\ntitle Sales 2024_Q1 & more\n")
	require.Empty(t, ds)
	require.Equal(t, "Sales2024_Q1&more", start.Document.Statements[0].Kind.(*parser.Title).Text.Value)
}

func TestMarkdownTextKeepsItsKind(t *testing.T) {
	start, ds := parse(t, "xychart\ntitle \"`*bold*`\"\n")
	require.Empty(t, ds)
	title := start.Document.Statements[0].Kind.(*parser.Title).Text
	require.True(t, title.Markdown)
	require.Equal(t, "*bold*", title.Value)
}

func TestAccessibilityStatements(t *testing.T) {
	start, ds := parse(t, "xychart\naccTitle: A title\naccDescr: A line\naccDescr {\nmulti\nline\n}\n")
	require.Empty(t, ds)
	require.Len(t, start.Document.Statements, 3)
	require.True(t, start.Document.Statements[0].Kind.(*parser.Accessibility).Title)
	require.True(t, start.Document.Statements[2].Kind.(*parser.Accessibility).Multiline)
}

func TestAxisModesPopAtLineEnd(t *testing.T) {
	start, ds := parse(t, "xychart\nx-axis 1 --> 5\nbar [1,2]\ny-axis 2 --> 3\n")
	require.Empty(t, ds)
	require.Len(t, start.Document.Statements, 3)
}

func TestKeywordsRequireAWordBoundary(t *testing.T) {
	_, ds := parse(t, "xychart\nbarx [1]\n")
	require.Len(t, ds, 1)
	require.Equal(t, "xychart/unknown-statement", ds[0].Code)
}

func TestDiagnostics(t *testing.T) {
	for _, c := range []struct {
		name, src, code, message string
		start, end               int
	}{
		{"trailing comma", "xychart\nbar [1, ]\n", "xychart/unexpected-token", "unexpected ], expected one of: NUMBER_WITH_DECIMAL", 16, 17},
		{"y band", "xychart\ny-axis [a, b]\n", "xychart/unexpected-token", "unexpected [, expected one of: ALPHA, AMP, BRKT, DOT, EQUALS, MD_STR, MINUS, MULT, NUM, NUMBER_WITH_DECIMAL, PLUS, STR, UNDERSCORE", 15, 16},
		{"unknown", "xychart\nfoo bar\nbar [1]\n", "xychart/unknown-statement", "unknown statement foo", 8, 15},
		{"open string", "xychart\ntitle \"abc\n", "xychart/unterminated", "unterminated \"", 14, 19},
		{"open list", "xychart\nbar [1, 2", "xychart/unterminated", "unterminated [", 12, 17},
		{"open description", "xychart\naccDescr {\nnever", "xychart/unterminated", "unterminated {", 17, 24},
	} {
		t.Run(c.name, func(t *testing.T) {
			_, ds := parse(t, c.src)
			require.NotEmpty(t, ds)
			d := ds[0]
			require.Equal(t, c.code, d.Code)
			require.Equal(t, source.Span{Start: c.start, End: c.end}, d.Span)
			require.Equal(t, c.message, d.Message)
		})
	}
}

func TestRecoveryContinuesAfterAnUnexpectedToken(t *testing.T) {
	start, ds := parse(t, "xychart\nbar [1, ]\nline [2]\n")
	require.Len(t, ds, 1)
	require.Len(t, start.Document.Statements, 1)
	require.True(t, start.Document.Statements[0].Kind.(*parser.PlotStatement).Line)
}
