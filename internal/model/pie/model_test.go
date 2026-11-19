package pie_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/model/pie"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/pie"
)

func resolve(src string) (*pie.Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	ast, _ := parser.Parse([]byte(src), prep.Removed)
	return pie.Resolve([]byte(src), ast)
}

type pair struct {
	label string
	value int64
	index int
}

func pairs(m *pie.Model) []pair {
	var out []pair
	for _, s := range m.Sections {
		out = append(out, pair{s.Label, s.Value, s.Index})
	}
	return out
}

func TestSectionsKeepDeclarationOrderAndThousandths(t *testing.T) {
	m, ds := resolve("pie showData\n\"B\" : 5\n\"A\" : 42.96\n\"C\" : 0\n\"D\" : 0.0005\n\"E\" : 1.2345\n")
	require.Empty(t, ds)
	require.True(t, m.ShowData)
	require.Equal(t, []pair{{"B", 5000, 0}, {"A", 42960, 1}, {"C", 0, 2}, {"D", 1, 3}, {"E", 1235, 4}}, pairs(m))
}

func TestDuplicateLabelKeepsFirstValueAndPosition(t *testing.T) {
	m, ds := resolve("pie\n\"a\" : 1\n\"b\" : 2\n\"a\" : 9\n\"c\" : 3\n")
	require.Empty(t, ds)
	require.Equal(t, []pair{{"a", 1000, 0}, {"b", 2000, 1}, {"c", 3000, 3}}, pairs(m))
}

func TestNegativeValuesAreRejectedBeforeDuplicateElimination(t *testing.T) {
	m, ds := resolve("pie\n\"a\" : 1\n\"a\" : -2\n\"b\" : -0.0004\n\"c\" : -0\n\"d\" : -0.0\n")
	require.Len(t, ds, 2)
	require.Equal(t, "pie/negative-value", ds[0].Code)
	require.Equal(t, "slice a has negative value -2", ds[0].Message)
	require.Equal(t, source.Span{Start: 18, End: 20}, ds[0].Span)
	require.Equal(t, "slice b has negative value -0.0004", ds[1].Message)
	require.Equal(t, []pair{{"a", 1000, 0}, {"c", 0, 3}, {"d", 0, 4}}, pairs(m))
}

func TestOverflowingValueSaturatesForTheLayoutToReject(t *testing.T) {
	m, ds := resolve("pie\n\"a\" : 99999999999\n")
	require.Empty(t, ds)
	require.Equal(t, pie.Overflow, m.Sections[0].Value)
}

func TestLabelsDecodeEntitiesAndEscapes(t *testing.T) {
	m, ds := resolve("pie\n\"a #35; b #amp; #zzz; #0;\" : 1\n\"q\\\"r\" : 2\n")
	require.Empty(t, ds)
	require.Equal(t, "a # b & #zzz; #0;", m.Sections[0].Label)
	require.Equal(t, "q\"r", m.Sections[1].Label)
}

func TestLastMetadataWinsAndEmptyIsIgnored(t *testing.T) {
	m, _ := resolve("pie\ntitle One\ntitle Two\naccTitle: t1\naccTitle: t2\naccDescr: d1\naccDescr: d2\n")
	require.Equal(t, "Two", m.Title)
	require.Equal(t, "t2", m.AccTitle)
	require.Equal(t, "d2", m.AccDescr)
	m, _ = resolve("pie\ntitle One\ntitle\naccTitle: t\naccTitle:\n")
	require.Empty(t, m.Title)
	require.Empty(t, m.AccTitle)
}

func TestFrontmatterTitleIsOverriddenByBodyTitle(t *testing.T) {
	m, _ := resolve("---\ntitle: Front\n---\npie\n\"a\" : 1\n")
	require.Equal(t, "Front", m.Title)
	m, _ = resolve("---\ntitle: Front\n---\npie\ntitle Body\n")
	require.Equal(t, "Body", m.Title)
	m, _ = resolve("---\ntitle: Front\n---\npie\ntitle\n")
	require.Equal(t, "Front", m.Title)
}

func TestHonouredConfig(t *testing.T) {
	for _, tc := range []struct {
		name   string
		source string
		want   []pie.ConfigEntry
	}{
		{"none", "pie\n", nil},
		{"frontmatter", "---\nconfig:\n  pie:\n    textPosition: 0.5\n    donutHole: 0.4\n---\npie\n", []pie.ConfigEntry{{Key: "donutHole", Value: 400}, {Key: "textPosition", Value: 500}}},
		{"directive", "%%{init: {\"pie\": {\"textPosition\": 0.9}}}%%\npie\n", []pie.ConfigEntry{{Key: "textPosition", Value: 900}}},
		{"directive overrides frontmatter", "---\nconfig:\n  pie:\n    textPosition: 0.2\n---\n%%{init: {\"pie\": {\"textPosition\": 0.3}}}%%\npie\n", []pie.ConfigEntry{{Key: "textPosition", Value: 300}}},
		{"out of range is ignored", "---\nconfig:\n  pie:\n    textPosition: 1.5\n    donutHole: 0.95\n---\npie\n", nil},
		{"negative is ignored", "---\nconfig:\n  pie:\n    donutHole: -0.1\n---\npie\n", nil},
		{"not a number is ignored", "---\nconfig:\n  pie:\n    donutHole: wide\n---\npie\n", nil},
		{"ignored keys are not kept", "---\nconfig:\n  pie:\n    legendPosition: bottom\n    highlightSlice: hover\n---\npie\n", nil},
		{"zero is kept", "---\nconfig:\n  pie:\n    textPosition: 0\n---\npie\n", []pie.ConfigEntry{{Key: "textPosition", Value: 0}}},
	} {
		m, _ := resolve(tc.source)
		require.Equal(t, tc.want, m.Config, tc.name)
	}
}

func TestThousandths(t *testing.T) {
	for _, tc := range []struct {
		literal  string
		value    int64
		negative bool
	}{
		{"0", 0, false}, {"10", 10000, false}, {"0.0005", 1, false}, {"0.0004", 0, false}, {"1.9995", 2000, false},
		{"-0", 0, false}, {"-0.000", 0, false}, {"-0.0004", 0, true}, {"-7", 7000, true}, {"+2.5", 2500, false},
	} {
		value, negative := pie.Thousandths(tc.literal)
		require.Equal(t, tc.value, value, tc.literal)
		require.Equal(t, tc.negative, negative, tc.literal)
	}
}
