package ishikawa

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(src string) (*Start, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func tokenKinds(src string) []string {
	s := newScanner(src, nil)
	var kinds []string
	for {
		token := s.next()
		kinds = append(kinds, token.Kind)
		if token.Kind == kindEnd {
			return kinds
		}
	}
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Message
	}
	return out
}

func texts(start *Start) []string {
	var out []string
	for _, item := range start.Document.Items {
		if item.Statement.Text != nil {
			out = append(out, item.Statement.Text.Text)
		}
	}
	return out
}

func TestLexerAppendsVirtualNewlineAndSplitsLines(t *testing.T) {
	require.Equal(t, []string{"ISHIKAWA", "NL", "SPACELIST", "TEXT", "NL", "EOF", "END"}, tokenKinds("ishikawa-beta\n  Effect"))
	require.Equal(t, []string{"ISHIKAWA", "SPACELINE", "EOF", "END"}, tokenKinds("ishikawa\n"))
	require.Equal(t, []string{"ISHIKAWA", "SPACELINE", "SPACELIST", "TEXT", "NL", "EOF", "END"}, tokenKinds("ishikawa  \n  Effect"))
}

func TestLexerFoldsHeaderAndTriesBetaFirst(t *testing.T) {
	for _, header := range []string{"ishikawa", "ISHIKAWA", "Ishikawa-Beta", "ishikawa-beta"} {
		start, ds := parse(header + "\n  Effect\n")
		require.Empty(t, ds, header)
		require.Equal(t, header, start.Header.Text)
	}
	require.Equal(t, []string{"ISHIKAWA", "TEXT", "NL", "EOF", "END"}, tokenKinds("ishikawa-betax"))
	require.Equal(t, []string{"TEXT", "NL", "EOF", "END"}, tokenKinds("ishikawax"))
	require.Equal(t, []string{"TEXT", "NL", "EOF", "END"}, tokenKinds("ishikawa_x"))
}

func TestTextTokenTakesWholeLine(t *testing.T) {
	start, ds := parse("ishikawa-beta\n  Effect\n    \"a\" {b} (c) [d]; e %% not a comment  \n")
	require.Empty(t, ds)
	require.Equal(t, []string{"Effect", `"a" {b} (c) [d]; e %% not a comment  `}, texts(start))
}

func TestCommentLinesAndBlankLinesAreWhitespaceStatements(t *testing.T) {
	start, ds := parse("%% lead\nishikawa-beta\n  %% note\n  Effect\n\n   \n  Cause\n")
	require.Empty(t, ds)
	require.Len(t, start.Leading, 2)
	require.Equal(t, []string{"Effect", "Cause"}, texts(start))
	blanks := 0
	for _, item := range start.Document.Items {
		if item.Statement.Blank != nil {
			blanks++
		}
	}
	require.Positive(t, blanks)
}

func TestIndentTokenIsRetainedSeparatelyFromText(t *testing.T) {
	src := "ishikawa-beta\n\t Effect\n        Cause\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	first, second := start.Document.Items[0].Statement, start.Document.Items[1].Statement
	require.Equal(t, "\t ", first.Indent.Text)
	require.Equal(t, "Effect", first.Text.Text)
	require.Equal(t, source.Span{Start: 14, End: 16}, first.Indent.Span)
	require.Equal(t, source.Span{Start: 16, End: 22}, first.Text.Span)
	require.Equal(t, source.Span{Start: 14, End: 22}, first.Span)
	require.Equal(t, 8, len(second.Indent.Text))
}

func TestSpansSkipRemovedRegions(t *testing.T) {
	src := "---\nx: y\n---\nishikawa-beta\n  Effect\n"
	start, ds := Parse([]byte(src), []source.Span{{Start: 0, End: 13}})
	require.Empty(t, ds)
	require.Equal(t, source.Span{Start: 13, End: 26}, start.Header.Span)
	require.Equal(t, source.Span{Start: 29, End: 35}, start.Document.Items[0].Statement.Text.Span)
}

func TestMissingHeader(t *testing.T) {
	_, ds := parse("Effect\n")
	require.Equal(t, []string{"unexpected Effect, expected one of: ISHIKAWA, SPACELINE"}, messages(ds))
	require.Equal(t, "ishikawa/unexpected-token", ds[0].Code)
	require.Equal(t, source.Span{Start: 0, End: 6}, ds[0].Span)
}

func TestHeaderWithoutDocumentIsRejected(t *testing.T) {
	_, ds := parse("ishikawa-beta")
	require.Equal(t, []string{"unexpected end of input, expected one of: SPACELINE, SPACELIST, TEXT"}, messages(ds))
	require.Equal(t, "ishikawa/unexpected-token", ds[0].Code)
	require.Equal(t, source.Span{Start: 13, End: 13}, ds[0].Span)
}

func TestHeaderLineEndIsABlankDocument(t *testing.T) {
	for _, src := range []string{"ishikawa-beta\n", "ishikawa\n\n\n", "ishikawa-beta  \n"} {
		start, ds := parse(src)
		require.Empty(t, ds, src)
		require.Empty(t, texts(start), src)
		require.NotEmpty(t, start.Document.Items, src)
	}
}

func TestBodyHeaderWordIsAStatementError(t *testing.T) {
	start, ds := parse("ishikawa-beta\n  Effect\nishikawa other\n  Cause\n")
	require.Equal(t, []string{"unknown statement ishikawa"}, messages(ds))
	require.Equal(t, "ishikawa/unknown-statement", ds[0].Code)
	require.Equal(t, source.Span{Start: 23, End: 37}, ds[0].Span)
	require.Equal(t, []string{"Effect", "Cause"}, texts(start))
}

func TestIndentedBodyHeaderWordIsAnIndentedError(t *testing.T) {
	start, ds := parse("ishikawa-beta\n  Effect\n  ishikawa-beta\n  Cause\n")
	require.Equal(t, []string{"unexpected ishikawa-beta, expected one of: EOF, NL, SPACELINE, TEXT"}, messages(ds))
	require.Equal(t, []string{"Effect", "Cause"}, texts(start))
}

func TestStatementWithoutIndentationIsAnEffectCandidate(t *testing.T) {
	start, ds := parse("ishikawa-beta\nEffect\n  Cause\n")
	require.Empty(t, ds)
	require.Nil(t, start.Document.Items[0].Statement.Indent)
	require.Equal(t, []string{"Effect", "Cause"}, texts(start))
}

func TestDocumentSpanAndStops(t *testing.T) {
	src := "ishikawa-beta\n  Effect\n\n\n  Cause"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, source.Span{Start: 0, End: len(src)}, start.Span)
	last := start.Document.Items[len(start.Document.Items)-1]
	require.Equal(t, "Cause", last.Statement.Text.Text)
	require.Equal(t, kindNL, last.Stop.Tokens[0].Kind)
}
