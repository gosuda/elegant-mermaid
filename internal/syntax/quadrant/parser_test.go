package quadrant_test

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/quadrant"
)

func parse(t *testing.T, text string) (*parser.Start, []diag.Diagnostic) {
	t.Helper()
	removed := syntax.Preprocess([]byte(text)).Removed
	return parser.Parse([]byte(text), removed)
}

func statements(start *parser.Start) []parser.StatementKind {
	var out []parser.StatementKind
	for _, line := range start.Document.Lines {
		if line.Statement.Kind != nil {
			out = append(out, line.Statement.Kind)
		}
	}
	return out
}

func TestCorpusParsesWithoutDiagnostics(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "quadrant", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		_, ds := parse(t, string(src))
		require.Empty(t, ds, path)
	}
}

func TestFullChartStatements(t *testing.T) {
	src := "quadrantChart\n  title Reach and engagement\n  x-axis Low Reach --> High Reach\n  y-axis Low --> High\n  quadrant-1 We should expand\n  quadrant-4 Re-evaluate\n  Campaign A: [0.3, 0.6]\n  Campaign B:::hot: [0.45, 0.23] radius: 20, color: #ff0000\n  classDef hot color: #908342, radius : 10\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	require.Equal(t, "QUADRANT", start.Header.Kind)
	kinds := statements(start)
	require.Len(t, kinds, 8)
	require.Equal(t, " Reach and engagement", kinds[0].(*parser.Title).Value.Text)
	x := kinds[1].(*parser.AxisDetails)
	require.False(t, x.Y)
	require.Equal(t, "Low Reach", x.First.Value)
	require.Equal(t, "High Reach", x.Second.Value)
	require.NotNil(t, x.Delimiter)
	y := kinds[2].(*parser.AxisDetails)
	require.True(t, y.Y)
	require.Equal(t, "High", y.Second.Value)
	q1 := kinds[3].(*parser.QuadrantDetails)
	require.Equal(t, 1, q1.Number)
	require.Equal(t, "We should expand", q1.Text.Value)
	q4 := kinds[4].(*parser.QuadrantDetails)
	require.Equal(t, 4, q4.Number)
	require.Equal(t, "Re-evaluate", q4.Text.Value)
	a := kinds[5].(*parser.Points)
	require.Equal(t, "Campaign A", a.Text.Value)
	require.Nil(t, a.Class)
	require.Equal(t, "0.3", a.PointX.Text)
	require.Equal(t, "0.6", a.PointY.Text)
	require.Nil(t, a.Styles)
	b := kinds[6].(*parser.Points)
	require.Equal(t, "hot", b.Class.Text)
	require.Len(t, b.Styles.Styles, 2)
	require.Equal(t, "radius: 20", b.Styles.Styles[0].Text)
	require.Equal(t, " color: #ff0000", b.Styles.Styles[1].Text)
	def := kinds[7].(*parser.ClassDefStatement)
	require.Equal(t, "hot", def.Name.Text)
	require.Len(t, def.Styles.Styles, 2)
	require.Equal(t, "radius : 10", def.Styles.Styles[1].Text[1:])
}

func TestHeaderAloneIsValid(t *testing.T) {
	for _, src := range []string{"quadrantChart", "quadrantChart\n", "  \n; quadrantChart  \n\n", "QUADRANTCHART\n"} {
		start, ds := parse(t, src)
		require.Empty(t, ds, src)
		require.Empty(t, statements(start), src)
	}
}

func TestAxisDelimiterVariants(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nx-axis Left -->\ny-axis Only\nx-axis Wide ---> Right\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 3)
	trailing := kinds[0].(*parser.AxisDetails)
	require.NotNil(t, trailing.Delimiter)
	require.Nil(t, trailing.Second)
	single := kinds[1].(*parser.AxisDetails)
	require.Nil(t, single.Delimiter)
	require.Equal(t, "Right", kinds[2].(*parser.AxisDetails).Second.Value)
}

func TestQuotedAndMarkdownTextKeepTheirKind(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nquadrant-2 \"(plain) text\"\nquadrant-3 \"`*bold*\ntwo`\"\n")
	require.Empty(t, ds)
	kinds := statements(start)
	plain := kinds[0].(*parser.QuadrantDetails).Text
	require.False(t, plain.Markdown)
	require.Equal(t, "(plain) text", plain.Value)
	require.Equal(t, len(plain.Value)+len(`""`), plain.Span.End-plain.Span.Start)
	require.Equal(t, len(plain.Value), plain.Content.End-plain.Content.Start)
	markdown := kinds[1].(*parser.QuadrantDetails).Text
	require.True(t, markdown.Markdown)
	require.Equal(t, "*bold*\ntwo", markdown.Value)
}

func TestCoordinateWildcardAcceptsAnyCharacterAfterZero(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nA: [0,5, 0x7]\nB: [1, 0]\n")
	require.Empty(t, ds)
	points := statements(start)
	require.Equal(t, "0,5", points[0].(*parser.Points).PointX.Text)
	require.Equal(t, "0x7", points[0].(*parser.Points).PointY.Text)
	require.Equal(t, "1", points[1].(*parser.Points).PointX.Text)
}

func TestKeywordsAreCaseInsensitive(t *testing.T) {
	start, ds := parse(t, "quadrantchart\nTITLE Up\nX-AXIS A --> B\nQuadrant-3 Z\nCLASSDEF c radius: 1\nACCTITLE: t\nAccDescr: d\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 6)
}

func TestSemicolonAndCommentsSeparateStatements(t *testing.T) {
	start, ds := parse(t, "quadrantChart\ntitle T; x-axis kept\nx-axis A; y-axis B\n%% comment\nquadrant-1 Q %% trailing\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 4)
}

func TestAccessibilityStatements(t *testing.T) {
	start, ds := parse(t, "quadrantChart\naccTitle: A title\naccDescr: A line\naccDescr {\nmulti\nline\n}\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 3)
	require.True(t, kinds[0].(*parser.Accessibility).Title)
	require.True(t, kinds[2].(*parser.Accessibility).Multiline)
}

func TestTitleAtEndOfInputHasAnEmptyValue(t *testing.T) {
	start, ds := parse(t, "quadrantChart\ntitle")
	require.Empty(t, ds)
	require.Equal(t, "", statements(start)[0].(*parser.Title).Value.Text)
}

func TestLineSpansIncludeTheTerminatorAndStatementsDoNot(t *testing.T) {
	src := "quadrantChart\n title Hello\n\nx-axis A\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	line := start.Document.Lines[1]
	require.Equal(t, "title Hello", src[line.Statement.Span.Start+1:line.Statement.Span.End])
	require.Equal(t, "\n\n", src[line.Eol.Span.Start:line.Eol.Span.End])
	require.Equal(t, line.Eol.Span.End, line.Span.End)
}

func TestDiagnostics(t *testing.T) {
	for _, c := range []struct {
		name, src, code, message string
		start, end               int
	}{
		{"missing point", "quadrantChart\nCampaign A\n", "quadrant/unexpected-token", "unexpected \n, expected one of: ALPHA, AMP, BRKT, COMMA, DOT, EQUALS, MINUS, MULT, NUM, PLUS, PUNCTUATION, SPACE, UNDERSCORE, UNICODE_TEXT, class_name, point_start", 24, 25},
		{"missing coordinate", "quadrantChart\nA: [\n", "quadrant/unterminated", "unterminated [", 17, 19},
		{"open point", "quadrantChart\nA: [0.1, 0.2", "quadrant/unterminated", "unterminated [", 17, 26},
		{"unclosed point bracket", "quadrantChart\nA: [0.1, 0.2\nB: [0.3, 0.4]\n", "quadrant/unexpected-token", "unexpected end of line, expected one of: EOF, NEWLINE, SEMI", 26, 26},
		{"open class name", "quadrantChart\nA:::", "quadrant/unterminated", "unterminated :::", 15, 18},
		{"trailing comma style", "quadrantChart\nA: [0.1, 0.2] radius: 3,\n", "quadrant/unexpected-token", "unexpected \n, expected one of: ALPHA, BRKT, COLON, MINUS, NUM, SPACE", 38, 39},
		{"unknown", "quadrantChart\n- foo\nx-axis A\n", "quadrant/unknown-statement", "unknown statement -", 14, 19},
		{"punctuation", "quadrantChart\nquadrant-1 (x)\n", "quadrant/unexpected-token", "unexpected (, expected one of: ALPHA, AMP, BRKT, COMMA, DOT, EQUALS, MD_STR, MULT, NUM, PLUS, PUNCTUATION, STR, UNDERSCORE, UNICODE_TEXT", 25, 26},
		{"open string", "quadrantChart\nx-axis \"abc\n", "quadrant/unterminated", "unterminated \"", 21, 26},
		{"open markdown", "quadrantChart\nx-axis \"`abc\n", "quadrant/unterminated", "unterminated \"`", 21, 27},
		{"open description", "quadrantChart\naccDescr {\nnever", "quadrant/unterminated", "unterminated {", 23, 30},
		{"two headers", "quadrantChart\nquadrantChart\n", "quadrant/unknown-statement", "unknown statement quadrantChart", 14, 27},
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
	start, ds := parse(t, "quadrantChart\nA: [0.1\ntitle Kept\n")
	require.Len(t, ds, 1)
	require.Len(t, statements(start), 1)
	require.Equal(t, " Kept", statements(start)[0].(*parser.Title).Value.Text)
}

func TestLexicalErrorInsideAPointResynchronises(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nA: [1.0, 0.2]\nB: [0.2, 0.3]\n")
	require.NotEmpty(t, ds)
	require.Equal(t, "quadrant/unexpected-token", ds[0].Code)
	require.NotEmpty(t, statements(start))
}

func TestQuotedTextTakesATailOfTokens(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nx-axis \"Low\" -- more --> \"High\"\n")
	require.Empty(t, ds)
	axis := statements(start)[0].(*parser.AxisDetails)
	require.Equal(t, "Low -- more", axis.First.Value)
	require.Equal(t, "High", axis.Second.Value)
}

func TestEntitiesAreOpaqueText(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nquadrant-1 Fish #amp; Chips #35; x\n")
	require.Empty(t, ds)
	require.Equal(t, "Fish #amp; Chips #35; x", statements(start)[0].(*parser.QuadrantDetails).Text.Value)
}

func TestBareHashAndSemicolonStillSplit(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nquadrant-1 a #b ; quadrant-2 c\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 2)
}

func TestTrailingSemicolonOfAColourLineIsDropped(t *testing.T) {
	start, ds := parse(t, "quadrantChart\nclassDef k color:#fff;\nA:::k: [0.1, 0.2]\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 2)
	_, ds = parse(t, "quadrantChart\nclassDef k color: #fff;\n")
	require.NotEmpty(t, ds)
}

func TestCarriageReturnEndsLineValues(t *testing.T) {
	start, ds := parse(t, "quadrantChart\rtitle One\rquadrant-1 Q\r\ntitle Two\r\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 3)
	require.Equal(t, " One", kinds[0].(*parser.Title).Value.Text)
	require.Equal(t, " Two", kinds[2].(*parser.Title).Value.Text)
}

func TestAccessibilityValueNeedsTextBeforeTheEnd(t *testing.T) {
	for _, src := range []string{"quadrantChart\naccTitle:", "quadrantChart\naccDescr: \n"} {
		_, ds := parse(t, src)
		require.Len(t, ds, 1, src)
		require.Equal(t, "quadrant/unexpected-token", ds[0].Code)
	}
}
