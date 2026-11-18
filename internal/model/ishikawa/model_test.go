package ishikawa

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/ishikawa"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	start, ds := syn.Parse([]byte(src), syntax.Preprocess([]byte(src)).Removed)
	m, rs := Resolve([]byte(src), start)
	return m, append(ds, rs...)
}

func shape(m *Model) []string {
	out := make([]string, len(m.Nodes))
	for i, n := range m.Nodes {
		out[i] = n.Label
		if n.Parent != NoParent {
			out[i] += "<" + m.Nodes[n.Parent].Label
		}
	}
	return out
}

func TestEffectCausesAndSubCauses(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  Effect\n    A\n      a1\n      a2\n    B\n      b1\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"Effect", "A<Effect", "a1<A", "a2<A", "B<Effect", "b1<B"}, shape(m))
	require.Equal(t, []int{1, 4}, m.Nodes[0].Children)
	require.Equal(t, []int{2, 3}, m.Nodes[1].Children)
	require.Equal(t, []int{0, 1, 2, 2, 1, 2}, depths(m))
}

func depths(m *Model) []int {
	out := make([]int, len(m.Nodes))
	for i, n := range m.Nodes {
		out[i] = n.Depth
	}
	return out
}

func TestEffectIndentationNeverSetsTheBase(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n      Effect\n  A\n    a1\n  B\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"Effect", "A<Effect", "a1<A", "B<Effect"}, shape(m))
}

func TestEqualIndentationMakesFlatCauses(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  Problem\n  Cause A\n  Subcause A1\n  Cause B\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"Problem", "Cause A<Problem", "Subcause A1<Problem", "Cause B<Problem"}, shape(m))
}

func TestSkippedLevelsAttachToThePreviousCause(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  E\n  A\n          deep\n    mid\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"E", "A<E", "deep<A", "mid<A"}, shape(m))
}

func TestDecreaseUsesTheStackNotSeenIndentation(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  E\n   A\n      x\n    y\n  z\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"E", "A<E", "x<A", "y<A", "z<E"}, shape(m))
}

func TestIndentationBelowTheFirstCauseIsLevelOne(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  E\n      A\n  B\n    C\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"E", "A<E", "B<E", "C<E"}, shape(m))
}

func TestTabCountsAsOneCodeUnit(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n\tE\n\t\tA\n\t\t\tB\n \t\tC\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"E", "A<E", "B<A", "C<A"}, shape(m))
}

func TestWhitespaceStatementsCreateNoNodeAndKeepTheStack(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  E\n    A\n%% note\n\n   \n      a\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"E", "A<E", "a<A"}, shape(m))
}

func TestHeaderOnlyIsAnEmptyModel(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n")
	require.Empty(t, ds)
	require.Empty(t, m.Nodes)
}

func TestLabelsAreTrimmedAndDecodedAndNeverMerged(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  Tea #9829; time   \n    x\n    x\n    #amp; &#38; #nope; #0;\n    accTitle: name\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"Tea ♥ time", "x", "x", "& && #nope; #0;", "accTitle: name"}, labels(m))
	require.Empty(t, m.AccTitle)
}

func labels(m *Model) []string {
	out := make([]string, len(m.Nodes))
	for i, n := range m.Nodes {
		out[i] = n.Label
	}
	return out
}

func TestNonBreakingSpacesTrimLikeJavaScript(t *testing.T) {
	m, ds := resolve("ishikawa-beta\n  \u00a0E\u3000\n")
	require.Empty(t, ds)
	require.Equal(t, "E", m.Nodes[0].Label)
}

func chain(depth int) string {
	var b strings.Builder
	b.WriteString("ishikawa-beta\n")
	for i := 0; i <= depth; i++ {
		b.WriteString(strings.Repeat(" ", i+1) + "n\n")
	}
	return b.String()
}

func TestDepthLimitIsSixtyFour(t *testing.T) {
	m, ds := resolve(chain(64))
	require.Empty(t, ds)
	require.Len(t, m.Nodes, 65)
	require.Equal(t, 64, m.Nodes[64].Depth)

	m, ds = resolve(chain(65))
	require.Len(t, ds, 1)
	require.Equal(t, "limit/nesting-depth", ds[0].Code)
	require.Equal(t, "nesting depth exceeds 64", ds[0].Message)
	require.Equal(t, "Reduce the nesting to 64 levels or fewer.", ds[0].Help)
	require.Len(t, m.Nodes, 65)
	last := len(chain(65)) - 2
	require.Equal(t, source.Span{Start: last, End: last + 1}, ds[0].Span)
}

func TestSiblingsAfterADroppedNodeStillAttach(t *testing.T) {
	src := chain(65) + strings.Repeat(" ", 3) + "after\n"
	m, ds := resolve(src)
	require.Len(t, ds, 1)
	require.Equal(t, "after", m.Nodes[len(m.Nodes)-1].Label)
	require.Equal(t, 2, m.Nodes[len(m.Nodes)-1].Depth)
}
