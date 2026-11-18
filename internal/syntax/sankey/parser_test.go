package sankey_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/sankey"
)

func parse(t *testing.T, text string) (*parser.Start, []diag.Diagnostic) {
	t.Helper()
	removed := syntax.Preprocess([]byte(text)).Removed
	return parser.Parse([]byte(text), removed)
}

func texts(start *parser.Start) [][3]string {
	var out [][3]string
	for _, r := range start.Csv.Records {
		out = append(out, [3]string{r.Source.Text(), r.Target.Text(), r.Value.Text()})
	}
	return out
}

func TestRecordsWithQuotedFieldsAndIndent(t *testing.T) {
	start, ds := parse(t, "sankey-beta\n\n  a,b,10\n\"x, y\",\"he said \"\"hi\"\"\",2.5\n")
	require.Empty(t, ds)
	require.Equal(t, "sankey-beta", start.Header.Text)
	require.Equal(t, [][3]string{{"  a", "b", "10"}, {"x, y", "he said \"\"hi\"\"", "2.5"}}, texts(start))
	require.True(t, start.OptEof.Present)
	require.Equal(t, 1, start.Csv.Records[1].Index)
}

func TestCommentLinesAreSkippedAndSpansStayInSource(t *testing.T) {
	text := "sankey\n%% note\na,b,1\n%% more\nc,d,2"
	start, ds := parse(t, text)
	require.Empty(t, ds)
	require.Equal(t, [][3]string{{"a", "b", "1"}, {"c", "d", "2"}}, texts(start))
	second := start.Csv.Records[1]
	require.Equal(t, "c,d,2", text[second.Span.Start:second.Span.End])
}

func TestLineEndRunsCollapseInsideQuotes(t *testing.T) {
	start, ds := parse(t, "sankey\n\"a\r\n\r\nb\",c,1")
	require.Empty(t, ds)
	require.Equal(t, [][3]string{{"a\nb", "c", "1"}}, texts(start))
}

func TestRejectedRecordsContributeNothing(t *testing.T) {
	start, ds := parse(t, "sankey\na,b\nc,d,1,e\nf,g,2")
	require.Len(t, ds, 2)
	require.Equal(t, "sankey/unexpected-token", ds[0].Code)
	require.Equal(t, "unexpected \n, expected one of: COMMA", ds[0].Message)
	require.Equal(t, "unexpected ,, expected one of: EOF, NEWLINE", ds[1].Message)
	require.Equal(t, [][3]string{{"f", "g", "2"}}, texts(start))
}

func TestEmptyFieldsArePreserved(t *testing.T) {
	cases := []struct {
		source string
		want   [3]string
	}{
		{"sankey\na,,1", [3]string{"a", "", "1"}},
		{"sankey\na,b,", [3]string{"a", "b", ""}},
		{"sankey\n\"\",b,1", [3]string{"", "b", "1"}},
		{"sankey\n,b,1", [3]string{"", "b", "1"}},
		{"sankey\n,,", [3]string{"", "", ""}},
	}
	for _, tc := range cases {
		start, ds := parse(t, tc.source)
		require.Empty(t, ds, tc.source)
		require.Equal(t, [][3]string{tc.want}, texts(start), tc.source)
	}
}

func TestInvalidCharactersAndHeaderOnly(t *testing.T) {
	_, ds := parse(t, "sankey\na,b,1\n\tc,d,2")
	require.Len(t, ds, 1)
	require.Equal(t, "sankey/unknown-statement", ds[0].Code)
	require.Equal(t, "unknown statement \t", ds[0].Message)
	_, ds = parse(t, "sankey\na,b,5é")
	require.Len(t, ds, 1)
	require.Equal(t, "unexpected é, expected one of: EOF, NEWLINE", ds[0].Message)
	_, ds = parse(t, "sankey\na,b,é")
	require.Len(t, ds, 1)
	require.Equal(t, "unexpected é, expected one of: DQUOTE, NON_ESCAPED_TEXT", ds[0].Message)
	_, ds = parse(t, "sankey\n")
	require.Len(t, ds, 1)
	require.Equal(t, "unexpected , expected one of: NEWLINE", ds[0].Message)
	require.Equal(t, 7, ds[0].Span.Start)
	require.Equal(t, 7, ds[0].Span.End)
}

func TestUnterminatedQuoteReportsOnlyItself(t *testing.T) {
	text := "sankey\na,b,1\n\"c,d,2\ne,f,3"
	start, ds := parse(t, text)
	require.Len(t, ds, 1)
	require.Equal(t, "sankey/unterminated", ds[0].Code)
	require.Equal(t, "unterminated \"", ds[0].Message)
	require.Equal(t, 13, ds[0].Span.Start)
	require.Equal(t, len(text), ds[0].Span.End)
	require.Equal(t, [][3]string{{"a", "b", "1"}}, texts(start))
}

func TestQuoteInsideUnquotedFieldRecoversPastQuotedNewline(t *testing.T) {
	start, ds := parse(t, "sankey\na\"x\ny\",b,1\nc,d,2")
	require.Len(t, ds, 1)
	require.Equal(t, "unexpected \", expected one of: COMMA", ds[0].Message)
	require.Equal(t, [][3]string{{"c", "d", "2"}}, texts(start))
}
