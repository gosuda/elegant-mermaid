package pie

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(src string) (*Pie, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func sections(p *Pie) [][2]string {
	var out [][2]string
	for _, s := range p.Body {
		if section, ok := s.Kind.(*PieSection); ok {
			out = append(out, [2]string{section.Label.Text, section.Number.Text})
		}
	}
	return out
}

func TestHeaderForms(t *testing.T) {
	for _, tc := range []struct {
		src      string
		showData bool
		sections int
	}{
		{"pie", false, 0},
		{"\n\npie\n", false, 0},
		{"pie showData", true, 0},
		{"pie showData\n\"a\": 1", true, 1},
		{"pie \"a\": 1", false, 1},
		{"pie showData \"a\": 1\n", true, 1},
		{"pie title x\n\"a\": 1", false, 1},
	} {
		p, ds := parse(tc.src)
		require.Empty(t, ds, tc.src)
		require.Equal(t, tc.showData, p.ShowData, tc.src)
		require.Len(t, sections(p), tc.sections, tc.src)
	}
}

func TestShowDataKeywordBoundary(t *testing.T) {
	_, ds := parse("pie showDataX\n")
	require.Equal(t, []string{"pie/unknown-statement: unknown statement showDataX"}, messages(ds))
	_, ds = parse("pie showData showData\n")
	require.Equal(t, []string{"pie/unknown-statement: unknown statement showData"}, messages(ds))
}

func TestSectionNumbers(t *testing.T) {
	for _, tc := range []struct{ number, ok string }{
		{"10", "10"}, {"0", "0"}, {"-3", "-3"}, {"42.96", "42.96"}, {"-0.5", "-0.5"}, {"007.5", "007.5"}, {"0.0", "0.0"},
	} {
		p, ds := parse("pie\n\"a\" : " + tc.number + "\n")
		require.Empty(t, ds, tc.number)
		require.Equal(t, [][2]string{{"a", tc.ok}}, sections(p), tc.number)
	}
	for _, number := range []string{"+5", ".5", "5.", "1e3", "007", "1,5", "NaN", "0x10", "1.2.3"} {
		_, ds := parse("pie\n\"a\" : " + number + "\n")
		require.NotEmpty(t, ds, number)
	}
}

func TestNumberLexingBacktracks(t *testing.T) {
	require.Equal(t, 1, integerLength("12."))
	require.Equal(t, 0, integerLength("1."))
	require.Equal(t, 0, integerLength("0."))
	require.Equal(t, 1, integerLength("007"))
	require.Equal(t, 3, floatLength("1.55.3"))
	require.Equal(t, 0, floatLength("1.5.3"))
	require.Equal(t, 3, floatLength("0.5"))
}

func TestStringForms(t *testing.T) {
	p, ds := parse("pie\n" +
		"\"double\" : 1\n" +
		"'single' : 2\n" +
		"\"it's\" : 3\n" +
		"'say \"x\"' : 4\n" +
		"\"a\\\"b\" : 5\n" +
		"\"tab\\there\" : 6\n" +
		"\"two\nlines\" : 7\n" +
		"\"% not a comment\" : 8\n" +
		"\"\" : 9\n")
	require.Empty(t, ds)
	var labels []string
	for _, s := range sections(p) {
		labels = append(labels, s[0])
	}
	require.Equal(t, []string{"double", "single", "it's", "say \"x\"", "a\"b", "tab\there", "two\nlines", "% not a comment", ""}, labels)
}

func TestStringTokenKeepsDelimitersInSpan(t *testing.T) {
	p, ds := parse("pie\n  \"a\\\"\" : 4\n")
	require.Empty(t, ds)
	section := p.Body[0].Kind.(*PieSection)
	require.Equal(t, "a\"", section.Label.Text)
	require.Equal(t, source.Span{Start: 6, End: 11}, section.Label.Span)
	require.Equal(t, source.Span{Start: 6, End: 15}, p.Body[0].Span)
}

func TestMetadata(t *testing.T) {
	p, ds := parse("pie\n  title   A   B  \n  accTitle:  T  x \n  accDescr: d %% c\naccDescr {\n  a  b\n\n  c\n}\ntitle\n\"a\" : 1")
	require.Empty(t, ds)
	require.Len(t, p.Body, 2)
	group := p.Body[0].Kind.(*TitleAndAccessibilities)
	var got [][2]string
	for _, item := range group.Items {
		got = append(got, [2]string{item.Field, item.Value})
	}
	require.Equal(t, [][2]string{{"title", "A B"}, {"accTitle", "T x"}, {"accDescr", "d"}, {"accDescr", "a b\nc"}, {"title", ""}}, got)
}

func TestInlineTitleOnHeaderLine(t *testing.T) {
	p, ds := parse("pie title Pets adopted\n\"a\" : 1")
	require.Empty(t, ds)
	require.Equal(t, "Pets adopted", p.Body[0].Kind.(*TitleAndAccessibilities).Items[0].Value)
}

func TestComments(t *testing.T) {
	p, ds := parse("pie %% header comment\n%% line\n\"a\" : 1 %% trailing\n  %% indented\n\"b\" : 2")
	require.Empty(t, ds)
	require.Equal(t, [][2]string{{"a", "1"}, {"b", "2"}}, sections(p))
}

func TestLineEndings(t *testing.T) {
	p, ds := parse("pie\r\n\"a\" : 1\r\"b\" : 2\n\n\n\"c\" : 3")
	require.Empty(t, ds)
	require.Len(t, sections(p), 3)
}

func TestSectionEndsAtLineEnd(t *testing.T) {
	_, ds := parse("pie\n\"a\" : 1 \"b\" : 2\n")
	require.Equal(t, []string{"pie/unexpected-token: unexpected \"b\", expected one of: EOF, NEWLINE"}, messages(ds))
	require.Equal(t, source.Span{Start: 12, End: 15}, ds[0].Span)
}

func TestErrorRecoverySkipsToNextLine(t *testing.T) {
	p, ds := parse("pie\n\"a\" 1 \"x\"\n\"b\" : 2\n")
	require.Len(t, ds, 1)
	require.Equal(t, "pie/missing-colon", ds[0].Code)
	require.Equal(t, [][2]string{{"b", "2"}}, sections(p))
}

func TestUnknownStatements(t *testing.T) {
	p, ds := parse("pie\nDogs : 1\n\"a\" : 1\nsemi ; colon\n")
	require.Len(t, ds, 2)
	require.Equal(t, "pie/unknown-statement: unknown statement semi", messages(ds)[0])
	require.Equal(t, "pie/label-requires-quotes", ds[1].Code)
	require.Equal(t, source.Span{Start: 4, End: 8}, ds[1].Span)
	require.Equal(t, [][2]string{{"a", "1"}}, sections(p))
}

func TestUnterminated(t *testing.T) {
	for _, tc := range []struct {
		src, token      string
		start, quoteEnd int
	}{
		{"pie\n\"abc", "\"", 4, 8},
		{"pie\n\"abc\\", "\"", 4, 9},
		{"pie\n'abc : 1\n\"x\" : 2", "'", 4, 8},
		{"pie\naccDescr {\n  never", "{", 13, 0},
	} {
		_, ds := parse(tc.src)
		require.Len(t, ds, 1, tc.src)
		assertUnterminatedPieDiagnostic(t, tc.src, tc.token, tc.start, tc.quoteEnd, ds[0])
	}
}

func TestBackslashBeforeLineEndIsNotAString(t *testing.T) {
	_, ds := parse("pie\n\"a\\\nb\" : 1\n")
	require.NotEmpty(t, ds)
	require.NotEqual(t, "pie/unterminated", ds[0].Code)
}

func TestKeywordsAreWordBounded(t *testing.T) {
	_, ds := parse("pie\npie : 1\n")
	require.Equal(t, []string{"pie/unknown-statement: unknown statement pie"}, messages(ds))
	_, ds = parse("pie\npie-chart : 1\n")
	require.Len(t, ds, 1)
	require.Equal(t, "pie/label-requires-quotes", ds[0].Code)
}

func TestRemovedSpansAreSkipped(t *testing.T) {
	src := "pie\n%%{init: {}}%%\n\"a\" : 1\n"
	p, ds := Parse([]byte(src), []source.Span{{Start: 4, End: 18}})
	require.Empty(t, ds)
	require.Equal(t, [][2]string{{"a", "1"}}, sections(p))
}

func TestMissingHeader(t *testing.T) {
	_, ds := parse("\"a\" : 1")
	require.Equal(t, []string{"pie/unexpected-token: unexpected \"a\", expected one of: pie"}, messages(ds))
}

func assertUnterminatedPieDiagnostic(t *testing.T, src, token string, start, quoteEnd int, d diag.Diagnostic) {
	t.Helper()
	if token == "{" {
		require.Equal(t, "pie/unterminated", d.Code, src)
		require.Equal(t, "unterminated "+token, d.Message, src)
		require.Equal(t, source.Span{Start: start, End: len(src)}, d.Span, src)
		return
	}
	require.Equal(t, "pie/quote-unclosed", d.Code, src)
	require.Equal(t, source.Span{Start: quoteEnd, End: quoteEnd}, d.Span, src)
}
