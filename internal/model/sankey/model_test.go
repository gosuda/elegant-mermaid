package sankey_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	model "github.com/gosuda/elegant-mermaid/internal/model/sankey"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/sankey"
)

func resolve(t *testing.T, text string) *model.Model {
	t.Helper()
	removed := syntax.Preprocess([]byte(text)).Removed
	start, ds := parser.Parse([]byte(text), removed)
	require.Empty(t, ds)
	m, rs := model.Resolve([]byte(text), start)
	require.Empty(t, rs)
	return m
}

func TestParseValuePrefixAndRounding(t *testing.T) {
	finite := func(n int64) model.Value { return model.Value{Kind: model.ValueFinite, Thousandths: n} }
	nonFinite := model.Value{Kind: model.ValueNonFinite}
	overflow := model.Value{Kind: model.ValueOverflow}
	for text, want := range map[string]model.Value{
		"124.729":      finite(124729),
		"0.0005":       finite(1),
		"0.0004999":    finite(0),
		"0.75":         finite(750),
		"1":            finite(1000),
		"+.5":          finite(500),
		"5.":           finite(5000),
		"5.e3":         finite(5000000),
		"1e3":          finite(1000000),
		"1e":           finite(1000),
		"1e+":          finite(1000),
		"12abc":        finite(12000),
		"0x10":         finite(0),
		"-0":           finite(0),
		"-2.5":         finite(-2500),
		"  7  ":        finite(7000),
		"2147483.647":  finite(2147483647),
		"2147483.648":  overflow,
		"1e400":        overflow,
		"1e-400":       finite(0),
		"00000000001e": finite(1000),
		"":             nonFinite,
		"x":            nonFinite,
		"-":            nonFinite,
		".":            nonFinite,
		".e5":          nonFinite,
		"Infinity":     nonFinite,
		"-Infinityx":   nonFinite,
		"infinity":     nonFinite,
	} {
		require.Equal(t, want, model.ParseValue(text), "%q", text)
	}
}

func TestResolveOrdersNodesSourceFirstAndKeepsDuplicates(t *testing.T) {
	m := resolve(t, "sankey\nb,a,1\na,b,2\n\"a\",b,3\nb,b,4\n")
	require.Equal(t, []string{"b", "a"}, []string{m.Nodes[0].ID, m.Nodes[1].ID})
	require.Len(t, m.Links, 4)
	require.Equal(t, [][2]int{{0, 1}, {1, 0}, {1, 0}, {0, 0}}, [][2]int{{m.Links[0].Source, m.Links[0].Target}, {m.Links[1].Source, m.Links[1].Target}, {m.Links[2].Source, m.Links[2].Target}, {m.Links[3].Source, m.Links[3].Target}})
}

func TestResolveTrimsUnquotesAndDecodesIds(t *testing.T) {
	m := resolve(t, "sankey\n  a b ,\"x \"\"q\"\" y\",1\n__proto__,A#35;,2\n")
	ids := []string{}
	for _, n := range m.Nodes {
		ids = append(ids, n.ID)
	}
	require.Equal(t, []string{"a b", "x \"q\" y", "__proto__", "A#"}, ids)
}

func TestResolveReadsHonouredConfigOnly(t *testing.T) {
	text := "---\nconfig:\n  sankey:\n    width: 410\n    nodeAlignment: left\n    showValues: false\n    nodeWidth: 15\n    height: 0\n---\n%%{init: {\"sankey\": {\"height\": 200, \"nodeAlignment\": \"bogus\"}}}%%\nsankey\na,b,1\n"
	m := resolve(t, text)
	got := map[string]model.DumpValue{}
	keys := []string{}
	for _, e := range m.Config {
		got[e.Key] = e.Value
		keys = append(keys, e.Key)
	}
	require.Equal(t, []string{"height", "nodeAlignment", "showValues", "width"}, keys)
	require.Equal(t, int64(200), got["height"].Integer)
	require.Equal(t, int64(410), got["width"].Integer)
	require.Equal(t, "left", got["nodeAlignment"].String)
	require.False(t, got["showValues"].Bool)
}
