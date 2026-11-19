package info

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func parse(src string) (*Info, []diag.Diagnostic) {
	return Parse([]byte(src), syntax.Preprocess([]byte(src)).Removed)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func TestAcceptedForms(t *testing.T) {
	for _, src := range []string{
		"info", "info\n", "\n\ninfo showInfo", "info\nshowInfo\n", "info %% note\nshowInfo %% note",
		"info showInfo title x", "info title x\naccTitle: t\naccDescr: d", "info\n\n\nshowInfo\n\ntitle t\n",
	} {
		doc, ds := parse(src)
		require.Empty(t, ds, src)
		require.Equal(t, "info", doc.Header.Kind)
	}
}

func TestShowInfoIsRecordedOnce(t *testing.T) {
	doc, ds := parse("info\nshowInfo\n")
	require.Empty(t, ds)
	require.NotNil(t, doc.ShowInfo)
	doc, _ = parse("info\n")
	require.Nil(t, doc.ShowInfo)
}

func TestMetadataKeepsLastValue(t *testing.T) {
	doc, ds := parse("info\ntitle one\ntitle  two  words\naccTitle: a\naccDescr {\n x\n  y\n}\n")
	require.Empty(t, ds)
	require.Equal(t, "two words", doc.Title.Text)
	require.Equal(t, "a", doc.AccTitle.Text)
	require.Equal(t, "x\ny", doc.AccDescr.Text)
}

func TestDiagnostics(t *testing.T) {
	cases := []struct {
		src  string
		want []string
	}{
		{"info\nshowInfo\nshowInfo\n", []string{"info/unexpected-token: unexpected showInfo, expected one of: ACC_DESCR, ACC_TITLE, EOF, TITLE"}},
		{"info\ntitle t\nshowInfo\n", []string{"info/unexpected-token: unexpected showInfo, expected one of: ACC_DESCR, ACC_TITLE, EOF, TITLE"}},
		{"info\nfoo bar\nshowInfo\n", []string{"info/unknown-statement: unknown statement foo"}},
		{"info foo\n", []string{"info/unknown-statement: unknown statement foo"}},
		{"info\n\"quoted\"\n", []string{"info/unknown-statement: unknown statement \"quoted\""}},
		{"info\naccDescr {\nnever closed", []string{"info/unterminated: unterminated {"}},
		{"infox\n", []string{"info/unexpected-token: unexpected infox, expected one of: info"}},
		{"info{\n", []string{"info/unexpected-token: unexpected info, expected one of: info"}},
	}
	for _, c := range cases {
		_, ds := parse(c.src)
		require.Equal(t, c.want, messages(ds), c.src)
	}
}

func TestUnknownStatementSpanRunsToLineEnd(t *testing.T) {
	src := "info\nfoo bar baz\nshowInfo"
	_, ds := parse(src)
	require.Len(t, ds, 1)
	require.Equal(t, "foo bar baz", src[ds[0].Span.Start:ds[0].Span.End])
}

func TestLineEndingsAreUniform(t *testing.T) {
	for _, eol := range []string{"\n", "\r\n", "\r"} {
		_, ds := parse("info" + eol + "showInfo" + eol + "title t" + eol)
		require.Empty(t, ds, "%q", eol)
	}
}
