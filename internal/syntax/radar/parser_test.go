package radar

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(src string) (*Start, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func TestHeaderForms(t *testing.T) {
	for src, header := range map[string]string{
		"radar-beta\naxis A":      "radar-beta",
		"radar-beta:\naxis A":     "radar-beta:",
		"radar-beta :\naxis A":    "radar-beta",
		"radar-beta\n\n\naxis A":  "radar-beta",
		"\n\nradar-beta":          "radar-beta",
		"radar-beta axis A":       "radar-beta",
		"radar-beta %% c\naxis A": "radar-beta",
	} {
		start, ds := parse(src)
		require.Empty(t, ds, src)
		require.Equal(t, header, start.Header.Kind, src)
	}
}

func TestHeaderNeedsBoundary(t *testing.T) {
	for _, src := range []string{"radar-betax", "radar-beta{", "radar-beta-1\n", "Radar-Beta\n"} {
		_, ds := parse(src)
		require.NotEmpty(t, ds, src)
		require.Equal(t, "radar/unexpected-token", ds[0].Code, src)
	}
}

func TestStatementForms(t *testing.T) {
	start, ds := parse("radar-beta\n" +
		"title  My   radar\n" +
		"accTitle: t\n" +
		"accDescr: d %% c\n" +
		"axis m[\"Math\"], s['Sci'], plain\n" +
		"curve a[\"Alice\"]{85, 90.5, 0}, b{\n  1,\n  2,\n  3\n}\n" +
		"curve k { m: 1, s 2, plain: 3 }\n" +
		"showLegend false, ticks 3\n" +
		"max 8 min 0\n" +
		"graticule polygon\n")
	require.Empty(t, ds)
	require.Equal(t, "My radar", start.Title.Value)
	require.Equal(t, "t", start.AccTitle.Value)
	require.Equal(t, "d", start.AccDescr.Value)
	require.Len(t, start.Axes, 3)
	require.Equal(t, "Math", start.Axes[0].Label.Value.Text)
	require.Equal(t, "Sci", start.Axes[1].Label.Value.Text)
	require.Nil(t, start.Axes[2].Label)
	require.Len(t, start.Curves, 3)
	require.Equal(t, []string{"85", "90.5", "0"}, numbers(start.Curves[0]))
	require.Equal(t, []string{"1", "2", "3"}, numbers(start.Curves[1]))
	require.Equal(t, "Alice", start.Curves[0].Label.Value.Text)
	for i, entry := range start.Curves[2].Entries {
		ref, keyed := entry.Reference()
		require.True(t, keyed)
		require.Equal(t, []string{"m", "s", "plain"}[i], ref.Text)
	}
	var names []string
	for _, o := range start.Options {
		names = append(names, o.Name.Kind+"="+o.Value.Text)
	}
	require.Equal(t, []string{"showLegend=false", "ticks=3", "max=8", "min=0", "graticule=polygon"}, names)
}

func numbers(c Curve) []string {
	var out []string
	for _, e := range c.Entries {
		out = append(out, e.Number().Text)
	}
	return out
}

func TestSpans(t *testing.T) {
	src := "radar-beta\naxis A[\"x\"] , B\ncurve c{1, 2}  %% tail\nmax 5\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, source.Span{Start: 16, End: 22}, start.Axes[0].Span)
	require.Equal(t, source.Span{Start: 25, End: 26}, start.Axes[1].Span)
	require.Equal(t, source.Span{Start: 33, End: 40}, start.Curves[0].Span)
	require.Equal(t, source.Span{Start: 0, End: len(src) - 1}, start.Span)
	require.Equal(t, source.Span{Start: 50, End: 55}, start.Options[0].Span)
}

func TestNumberTokenFollowsTheAuthorityPattern(t *testing.T) {
	for src, want := range map[string]int{"0": 1, "7": 1, "42": 2, "1.5": 3, "0.5": 3, "12.25": 5, "01": 1, "007": 1, "1.": 0, "12.": 1, ".5": 0, "1.2.3": 0, "1.25.3": 3, "x": 0} {
		require.Equal(t, want, numberLength(src), src)
	}
}

func TestIdentifierTokenFollowsTheAuthorityPattern(t *testing.T) {
	for src, want := range map[string]int{"a": 1, "a-b": 3, "a-": 1, "a--": 1, "a-b-": 3, "_x": 2, "3d": 2, "-a": 0, "a.b": 1, "é": 0} {
		require.Equal(t, want, idLength(src), src)
	}
}

func TestKeywordsYieldToLongerIdentifiers(t *testing.T) {
	start, ds := parse("radar-beta\naxis maximum, axis-1, ticks2\n")
	require.Empty(t, ds)
	require.Len(t, start.Axes, 3)
	for _, src := range []string{"radar-beta\naxis axis\n", "radar-beta\naxis max\n", "radar-beta\naxis true\n", "radar-beta\ncurve circle {1}\n", "radar-beta\naxis 3d\n"} {
		_, ds = parse(src)
		require.NotEmpty(t, ds, src)
	}
}

func TestStringEscapes(t *testing.T) {
	start, ds := parse("radar-beta\naxis A[\"a\\\"b\\nc\\\\d\\q\"]\n")
	require.Empty(t, ds)
	require.Equal(t, "a\"b\nc\\dq", start.Axes[0].Label.Value.Text)
	start, ds = parse("radar-beta\naxis A[\"two\nlines\"]\n")
	require.Empty(t, ds)
	require.Equal(t, "two\nlines", start.Axes[0].Label.Value.Text)
	_, ds = parse("radar-beta\naxis A[\"x\\\ny\"]\n")
	require.NotEmpty(t, ds)
}

func TestCurveEntryRules(t *testing.T) {
	for src, want := range map[string]string{
		"radar-beta\ncurve c {}\n":       "radar/unexpected-token: unexpected }, expected one of: ID, NUMBER",
		"radar-beta\ncurve c {1,}\n":     "radar/unexpected-token: unexpected }, expected one of: NUMBER",
		"radar-beta\ncurve c {A 1, 2}\n": "radar/unexpected-token: unexpected 2, expected one of: ID",
		"radar-beta\ncurve c {1, B 2}\n": "radar/unexpected-token: unexpected B, expected one of: NUMBER",
		"radar-beta\ncurve c {1\n,2}\n":  "radar/unexpected-token: unexpected ,, expected one of: }",
		"radar-beta\ncurve c 1\n":        "radar/unexpected-token: unexpected 1, expected one of: {",
		"radar-beta\ncurve c {-3}\n":     "radar/unexpected-token: unexpected -, expected one of: ID, NUMBER",
		"radar-beta\ncurve c {01}\n":     "radar/unexpected-token: unexpected 1, expected one of: }",
		"radar-beta\nshowLegend yes\n":   "radar/unexpected-token: unexpected yes, expected one of: BOOLEAN",
		"radar-beta\ngraticule square\n": "radar/unexpected-token: unexpected square, expected one of: GRATICULE",
		"radar-beta\ntitlefoo\n":         "radar/unexpected-token: unexpected foo, expected one of: EOF, NEWLINE",
		"radar-beta\naxis A,\n":          "radar/unexpected-token: unexpected \n, expected one of: ID",
		"radar-beta\naxis A; axis B\n":   "radar/unknown-statement: unknown statement ;",
	} {
		_, ds := parse(src)
		require.NotEmpty(t, ds, src)
		require.Contains(t, messages(ds), want, src)
	}
}

func TestRecoveryContinuesAfterARejectedStatement(t *testing.T) {
	start, ds := parse("radar-beta\naxis A, 5\ncurve c {1,}\ncurve ok {2}\naxis B\n")
	require.Equal(t, []string{
		"radar/unexpected-token: unexpected 5, expected one of: ID",
		"radar/unexpected-token: unexpected }, expected one of: NUMBER",
	}, messages(ds))
	require.Len(t, start.Axes, 2)
	require.Len(t, start.Curves, 1)
	require.Equal(t, "ok", start.Curves[0].Name.Text)
}

func TestRecoveryInsideBracesStopsAtTheClosingBrace(t *testing.T) {
	start, ds := parse("radar-beta\ncurve c {1,\n  oops 2,\n  3} axis B\n")
	require.Len(t, ds, 1)
	require.Len(t, start.Axes, 1)
	require.Equal(t, "B", start.Axes[0].Name.Text)
}

func TestUnknownStatementSpansTheLine(t *testing.T) {
	src := "radar-beta\nfoo bar \"baz\"\naxis A\n"
	start, ds := parse(src)
	require.Equal(t, []string{"radar/unknown-statement: unknown statement foo"}, messages(ds))
	require.Equal(t, source.Span{Start: 11, End: 24}, ds[0].Span)
	require.Len(t, start.Axes, 1)
}

func TestUnknownStatementSkipsCurveBraces(t *testing.T) {
	src := "radar-beta\nfoo {\n1}\naxis A\n"
	start, ds := parse(src)
	require.Equal(t, []string{"radar/unknown-statement: unknown statement foo"}, messages(ds))
	require.Equal(t, source.Span{Start: 11, End: 19}, ds[0].Span)
	require.Len(t, start.Axes, 1)
}

func TestUnterminatedProducesOnlyTheOpenerDiagnostic(t *testing.T) {
	for src, opener := range map[string]source.Span{
		"radar-beta\naxis A[\"abc":             {Start: 18, End: 22},
		"radar-beta\naxis A['abc\naxis B":      {Start: 18, End: 29},
		"radar-beta\naccDescr {\nnever closed": {Start: 20, End: 34},
		"radar-beta\naxis A[\"x\\":             {Start: 18, End: 21},
	} {
		_, ds := parse(src)
		require.Len(t, ds, 1, src)
		require.Equal(t, "radar/unterminated", ds[0].Code, src)
		require.Equal(t, opener, ds[0].Span, src)
	}
}

func TestMetadataValues(t *testing.T) {
	src := "radar-beta\ntitle   My   diagram \naccTitle:  T\t\t t \naccDescr: d %% c\naccDescr {\n  one   two\n\n  three  \n}\ntitle\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "", start.Title.Value)
	require.Equal(t, "T t", start.AccTitle.Value)
	require.Equal(t, "one two\nthree", start.AccDescr.Value)
}

func TestCommentsAndLineEndings(t *testing.T) {
	start, ds := parse("radar-beta\r\n%% only a comment\r\naxis A %% trailing\r\n\r\ncurve c {1}\raxis B\n")
	require.Empty(t, ds)
	require.Len(t, start.Axes, 2)
	require.Len(t, start.Curves, 1)
}

func TestRemovedSpansAreSkipped(t *testing.T) {
	src := "---\ntitle: x\n---\nradar-beta\naxis A\n"
	start, ds := Parse([]byte(src), []source.Span{{Start: 0, End: 17}})
	require.Empty(t, ds)
	require.Equal(t, "radar-beta", start.Header.Kind)
	require.Len(t, start.Axes, 1)
}

func TestNestedBracesDoNotRecurse(t *testing.T) {
	depth := 4096
	src := "radar-beta\ncurve c {" + strings.Repeat("{", depth) + "\n"
	_, ds := parse(src)
	require.NotEmpty(t, ds)
}
