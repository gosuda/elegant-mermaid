package cynefin

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func parse(src string) (*Cynefin, []diag.Diagnostic) {
	return Parse([]byte(src), syntax.Preprocess([]byte(src)).Removed)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func TestHeaderForms(t *testing.T) {
	for _, src := range []string{"cynefin-beta", "cynefin-beta:", "\n\ncynefin-beta\n", "cynefin-beta %% note\ncomplex", "cynefin-beta:complex"} {
		doc, ds := parse(src)
		require.Empty(t, ds, src)
		require.Contains(t, []string{"cynefin-beta", "cynefin-beta:"}, doc.Header.Kind, src)
	}
}

func TestHeaderGuardRejectsGluedText(t *testing.T) {
	_, ds := parse("cynefin-betax")
	require.Equal(t, []string{"cynefin/unexpected-token: unexpected cynefin-betax, expected one of: cynefin-beta, cynefin-beta:"}, messages(ds))
}

func TestDomainBlocksAndTransitions(t *testing.T) {
	src := "cynefin-beta\n  title T\n  complex \"a\" 'b'\n\n  \"c\"\n  clear\n  complicated --> clear : \"x\"\n  chaotic --> complex\n"
	doc, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "T", doc.Title.Text)
	require.Len(t, doc.Domains, 2)
	require.Equal(t, "complex", doc.Domains[0].Domain.Text)
	require.Len(t, doc.Domains[0].Items, 3)
	require.Equal(t, "b", doc.Domains[0].Items[1].Label.Text)
	require.Empty(t, doc.Domains[1].Items)
	require.Len(t, doc.Transitions, 2)
	require.Equal(t, "x", doc.Transitions[0].Label.Text)
	require.Nil(t, doc.Transitions[1].Label)
}

func TestDomainSpansCoverItemsOnly(t *testing.T) {
	src := "cynefin-beta\ncomplex\n\"one\"\n\n\"two\"\n\n%% c\nclear\n"
	doc, ds := parse(src)
	require.Empty(t, ds)
	first := doc.Domains[0]
	require.Equal(t, source.Span{Start: 13, End: 33}, first.Span)
	require.Equal(t, "complex\n\"one\"\n\n\"two\"", src[first.Span.Start:first.Span.End])
	require.Equal(t, "clear", src[doc.Domains[1].Span.Start:doc.Domains[1].Span.End])
}

func TestTransitionSpanExcludesLineEnd(t *testing.T) {
	src := "cynefin-beta\ncomplex --> clear : \"go\" %% note\n"
	doc, ds := parse(src)
	require.Empty(t, ds)
	span := doc.Transitions[0].Span
	require.Equal(t, "complex --> clear : \"go\"", src[span.Start:span.End])
}

func TestMetadataLastValueWins(t *testing.T) {
	doc, ds := parse("cynefin-beta\ntitle  a   b\naccTitle: t1\naccDescr: d1\ntitle second\naccTitle: t2 %% c\naccDescr {\n  multi\n    line\n}\n")
	require.Empty(t, ds)
	require.Equal(t, "second", doc.Title.Text)
	require.Equal(t, "t2", doc.AccTitle.Text)
	require.Equal(t, "multi\nline", doc.AccDescr.Text)
}

func TestDiagnostics(t *testing.T) {
	cases := []struct {
		src  string
		want []string
	}{
		{"cynefin-beta\ncomplex -->", []string{"cynefin/unexpected-token: unexpected end of input, expected one of: DOMAIN_NAME"}},
		{"cynefin-beta\nfoo\ncomplex\n", []string{"cynefin/unknown-statement: unknown statement foo"}},
		{"cynefin-beta\n--> clear\n", []string{"cynefin/unknown-statement: unknown statement -->"}},
		{"cynefin-beta\ncomplex --> \"x\"\n", []string{"cynefin/unexpected-token: unexpected \"x\", expected one of: DOMAIN_NAME"}},
		{"cynefin-beta\ncomplex --> clear :\n", []string{"cynefin/unexpected-token: unexpected \n, expected one of: STRING"}},
		{"cynefin-beta\ncomplex --> clear extra\n", []string{"cynefin/unexpected-token: unexpected extra, expected one of: :, EOF, NEWLINE"}},
		{"cynefin-beta\ncomplex --> clear : \"x\" extra\n", []string{"cynefin/unexpected-token: unexpected extra, expected one of: EOF, NEWLINE"}},
		{"cynefin-beta\ncomplex \"never closed\n", []string{"cynefin/unterminated: unterminated \""}},
		{"cynefin-beta\naccDescr {\nnever closed", []string{"cynefin/unterminated: unterminated {"}},
		{"cynefin-beta\n5 6\n", []string{"cynefin/unknown-statement: unknown statement 5"}},
	}
	for _, c := range cases {
		_, ds := parse(c.src)
		require.Equal(t, c.want, messages(ds), c.src)
	}
}

func TestRejectedStatementsProduceNothing(t *testing.T) {
	doc, ds := parse("cynefin-beta\ncomplex --> clear extra\nchaotic --> complex\n")
	require.Len(t, ds, 1)
	require.Len(t, doc.Transitions, 1)
	require.Equal(t, "chaotic", doc.Transitions[0].From.Text)
}

func TestDomainNamesAreCaseSensitivePrefixes(t *testing.T) {
	doc, ds := parse("cynefin-beta\nComplex\ncomplexity\n")
	require.Equal(t, []string{"cynefin/unknown-statement: unknown statement Complex", "cynefin/unknown-statement: unknown statement ity"}, messages(ds))
	require.Len(t, doc.Domains, 1)
	require.Equal(t, "complex", doc.Domains[0].Domain.Text)
}

func TestStringEscapes(t *testing.T) {
	doc, ds := parse("cynefin-beta\nclear \"a\\\"b\\n\\x\"\n")
	require.Empty(t, ds)
	require.Equal(t, "a\"b\nx", doc.Domains[0].Items[0].Label.Text)
}

func TestLineEndingsAreUniform(t *testing.T) {
	for _, eol := range []string{"\n", "\r\n", "\r"} {
		doc, ds := parse("cynefin-beta" + eol + "complex" + eol + "\"a\"" + eol + "complex --> clear" + eol)
		require.Empty(t, ds, "%q", eol)
		require.Len(t, doc.Domains[0].Items, 1)
		require.Len(t, doc.Transitions, 1)
	}
}
