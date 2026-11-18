package venn_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/venn"
)

func parse(t *testing.T, text string) (*parser.Start, []diag.Diagnostic) {
	t.Helper()
	removed := syntax.Preprocess([]byte(text)).Removed
	return parser.Parse([]byte(text), removed)
}

func statements(start *parser.Start) []parser.StatementKind {
	var out []parser.StatementKind
	for _, line := range start.Document.Lines {
		if line.Statement != nil {
			out = append(out, line.Statement.Kind)
		}
	}
	return out
}

func TestFullStatements(t *testing.T) {
	src := "venn-beta\n  title Overlap\n  set A[\"Alpha\"]:20\n    text \"x\"\n  set B\n  union A,B[\"AB\"]:3\n  style A fill:#ff6b6b, color:rgb(1, 2, 3)\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 6)
	require.Equal(t, "title Overlap", kinds[0].(*parser.Title).Token.Text)
	set := kinds[1].(*parser.Set)
	require.Equal(t, "A", set.ID.Text)
	require.Equal(t, "Alpha", set.Label.Text)
	require.Equal(t, "20", set.Size.Text)
	require.Equal(t, "\"x\"", kinds[2].(*parser.IndentedText).Tail.ID.Text)
	union := kinds[4].(*parser.Union)
	require.Len(t, union.IDs.IDs, 2)
	require.Equal(t, "AB", union.Label.Text)
	style := kinds[5].(*parser.Style)
	require.Len(t, style.Styles.Fields, 2)
	require.Equal(t, "#ff6b6b", style.Styles.Fields[0].Value.Tokens.Tokens[0].Text)
	require.Equal(t, "rgb(1, 2, 3)", style.Styles.Fields[1].Value.Tokens.Tokens[0].Text)
}

func TestTitleEndsAtEveryLineEnding(t *testing.T) {
	for _, eol := range []string{"\n", "\r\n", "\r"} {
		start, ds := parse(t, "venn-beta"+eol+"  title Overlap"+eol+"  set A"+eol+"  set B"+eol)
		require.Empty(t, ds, "%q", eol)
		kinds := statements(start)
		require.Len(t, kinds, 3, "%q", eol)
		require.Equal(t, "title Overlap", kinds[0].(*parser.Title).Token.Text, "%q", eol)
	}
}

func TestSeveralStatementsShareALine(t *testing.T) {
	start, ds := parse(t, "venn-beta set A set B union A,B\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 3)
}

func TestKeywordsRequireAWordBoundary(t *testing.T) {
	for _, src := range []string{"venn-beta\n  setA\n", "venn-beta\n  set A\n  stylea fill:red\n", "venn-beta\n  set A\n  set B\n  unionA,B\n"} {
		_, ds := parse(t, src)
		require.NotEmpty(t, ds, src)
		require.Equal(t, "venn/unknown-statement", ds[0].Code, src)
	}
}

func TestIndentedTextNeedsIndentMode(t *testing.T) {
	start, ds := parse(t, "venn-beta\n  set A\n  text x\n\n  text y\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 3)
	_, isIndented := statements(start)[2].(*parser.IndentedText)
	require.True(t, isIndented)
	start, ds = parse(t, "venn-beta\n  set A\n  style A fill:red\n  text A x\n")
	require.Empty(t, ds)
	explicit, ok := statements(start)[2].(*parser.Text)
	require.True(t, ok)
	require.Equal(t, "x", explicit.ID.Text)
}

func TestCommentsInsideStatements(t *testing.T) {
	start, ds := parse(t, "venn-beta\n  set A %% note\n%% whole line\n  text x\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 2)
	_, ds = parse(t, "venn-beta\n  set A%% note\n")
	require.NotEmpty(t, ds)
}

func TestBracketLabelsAreTrimmedOrQuoted(t *testing.T) {
	start, ds := parse(t, "venn-beta\n  set A[ one two ]\n  set B[\"  two ]\"]\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Equal(t, "one two", kinds[0].(*parser.Set).Label.Text)
	require.Equal(t, "  two ]", kinds[1].(*parser.Set).Label.Text)
}

func TestDiagnostics(t *testing.T) {
	for _, c := range []struct {
		name, src, code, message string
		start, end               int
	}{
		{"missing identifier", "venn-beta\n  set", "venn/unexpected-token", "unexpected end of input, expected one of: IDENTIFIER, STRING", 15, 15},
		{"missing size", "venn-beta\n  set A:", "venn/unexpected-token", "unexpected end of input, expected one of: NUMERIC", 18, 18},
		{"unknown", "venn-beta\n  foo bar\n  set A\n", "venn/unknown-statement", "unknown statement foo", 12, 19},
		{"open label", "venn-beta\n  set A[\"x\n", "venn/unterminated", "unterminated [", 17, 21},
		{"open string", "venn-beta\n  set \"abc\n", "venn/unterminated", "unterminated \"", 16, 21},
		{"text id", "venn-beta\n  set A\n  style A fill:red\n  text x\n", "venn/unexpected-token", "unexpected \n, expected one of: COMMA, IDENTIFIER, NUMERIC, STRING", 45, 46},
		{"style value", "venn-beta\n  set A\n  style A fill:,\n", "venn/unexpected-token", "unexpected ,, expected one of: HEXCOLOR, IDENTIFIER, NUMERIC, RGBACOLOR, RGBCOLOR, STRING", 33, 34},
		{"invalid byte", "venn-beta\n  set A;\n", "venn/unknown-statement", "unknown statement ;", 17, 18},
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
	start, ds := parse(t, "venn-beta\n  set\n  set A\n")
	require.Len(t, ds, 1)
	require.Len(t, statements(start), 1)
}

func TestRemovedSpansAreInvisibleToTheLexer(t *testing.T) {
	start, ds := parse(t, "---\ntitle: front\n---\nvenn-beta\n  set A\n  %%{init: {}}%%\n  text x\n")
	require.Empty(t, ds)
	require.Len(t, statements(start), 2)
}
