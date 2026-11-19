package venn_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/venn"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/venn"
)

func resolve(text string) (*model.Model, []diag.Diagnostic) {
	start, parsed := parser.Parse([]byte(text), syntax.Preprocess([]byte(text)).Removed)
	m, resolved := model.Resolve([]byte(text), start)
	return m, append(parsed, resolved...)
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func TestThousandthsRoundsHalfAwayFromZero(t *testing.T) {
	for literal, want := range map[string]int64{
		"1": 1000, "0.0005": 1, "0.0004": 0, "-0.0005": -1, "2.5": 2500, ".5": 500, "007": 7000,
	} {
		require.Equal(t, want, model.Thousandths(literal), literal)
	}
}

func TestSetsKeepFirstSpanAndLastValue(t *testing.T) {
	m, ds := resolve("venn-beta\n  set A:2\n  set B\n  set A[\"Again\"]:3\n")
	require.Empty(t, ds)
	sets := m.Sets()
	require.Len(t, sets, 2)
	require.Equal(t, "Again", sets[0].Display)
	require.Equal(t, int64(3000), sets[0].Size)
	require.Equal(t, 12, sets[0].Span.Start)
}

func TestDefaultSizesFollowTheSetCount(t *testing.T) {
	m, _ := resolve("venn-beta\n  set A\n  set B\n  union A,B\n")
	var sizes []int64
	for _, s := range m.Subsets {
		sizes = append(sizes, s.Size)
	}
	require.Equal(t, []int64{10000, 10000, 2500}, sizes)
}

func TestIndentedTextAttachesToTheLatestSubset(t *testing.T) {
	m, ds := resolve("venn-beta\n  set A\n    text one\n  set B\n    text two\n")
	require.Empty(t, ds)
	require.Len(t, m.Texts, 2)
	require.Equal(t, []string{"A"}, m.Texts[0].Sets)
	require.Equal(t, []string{"B"}, m.Texts[1].Sets)
}

func TestExplicitTextSortsItsTargets(t *testing.T) {
	m, ds := resolve("venn-beta\n  set A\n  set B\n  title t\n  text B,A hello\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"A", "B"}, m.Texts[0].Sets)
}

func TestSetCountDiagnostics(t *testing.T) {
	_, none := resolve("venn-beta\n")
	require.Equal(t, []string{"venn/no-sets"}, codes(none))
	_, many := resolve("venn-beta\n  set A\n  set B\n  set C\n  set D\n")
	require.Equal(t, []string{"venn/too-many-sets"}, codes(many))
	require.Equal(t, 36, many[0].Span.Start)
}

func TestUnionRules(t *testing.T) {
	_, short := resolve("venn-beta\n  set A\n  union A\n")
	require.Equal(t, []string{"venn/union-requires-multiple-identifiers"}, codes(short))
	_, unknown := resolve("venn-beta\n  set A\n  union A,B,C\n")
	require.Equal(t, []string{"venn/unknown-set-identifier"}, codes(unknown))
	require.Len(t, unknown[0].Related, 1)
	require.Equal(t, "unknown set identifier: B, C", unknown[0].Message)
}

func TestIndentedTextBeforeAnySetIsAnUnexpectedToken(t *testing.T) {
	_, ds := resolve("venn-beta\n    text one\n  set A\n")
	require.Equal(t, []string{"venn/unexpected-token"}, codes(ds))
}

func TestTitleAndConfigAreRead(t *testing.T) {
	m, ds := resolve("---\ntitle: Front #amp;\nconfig:\n  venn:\n    width: 400\n---\nvenn-beta\n  title Inline\n  set A\n")
	require.Empty(t, ds)
	require.Equal(t, "Inline", m.Title)
	width, ok := m.Integer("width")
	require.True(t, ok)
	require.Equal(t, int64(400), width)
}

func TestEntitiesDecodeInLabels(t *testing.T) {
	m, _ := resolve("venn-beta\n  set A[\"a #38; b\"]\n")
	require.Equal(t, "a & b", m.Sets()[0].Display)
}

func TestStyleEntriesKeepTheLastValue(t *testing.T) {
	m, _ := resolve("venn-beta\n  set A\n  style A fill:#ff0000, fill:#00ff00\n")
	require.Len(t, m.Styles[0].Entries, 1)
	require.Equal(t, "#00ff00", m.Styles[0].Entries[0].Value)
}
