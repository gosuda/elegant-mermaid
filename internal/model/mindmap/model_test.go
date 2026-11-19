package mindmap

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/mindmap"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	pre := syntax.Preprocess([]byte(src))
	start, parsed := syn.Parse([]byte(src), pre.Removed)
	m, resolved := Resolve([]byte(src), start)
	return m, append(parsed, resolved...)
}

func shape(t *testing.T, node string) Shape {
	t.Helper()
	m, ds := resolve("mindmap\n  " + node + "\n")
	require.Empty(t, ds, node)
	return m.Nodes[0].Shape
}

func TestShapeFollowsOpenerAndCloser(t *testing.T) {
	for node, want := range map[string]Shape{
		"a":        ShapeDefault,
		"a[b]":     ShapeSquare,
		"a[b)":     ShapeSquare,
		"a(b)":     ShapeRounded,
		"a(b]":     ShapeCloud,
		"a(b))":    ShapeCloud,
		"a((b))":   ShapeCircle,
		"a((b)":    ShapeCircle,
		"a)b(":     ShapeCloud,
		"a))b))":   ShapeBang,
		"a{{b}}":   ShapeHexagon,
		"a(-b-)":   ShapeDefault,
		"a-)b(-":   ShapeCloud,
		"((b))":    ShapeCircle,
		"a[\"b\"]": ShapeSquare,
	} {
		require.Equal(t, want, shape(t, node), node)
	}
}

func TestIdsAndDescriptions(t *testing.T) {
	m, ds := resolve("mindmap\n  root  \n    x[ y ]\n    ((z))\n    x[w]\n")
	require.Empty(t, ds)
	require.Equal(t, "root  ", m.Nodes[0].SourceID)
	require.Equal(t, "root", m.Nodes[0].Label)
	require.Equal(t, "x", m.Nodes[1].SourceID)
	require.Equal(t, " y ", m.Nodes[1].Description)
	require.Equal(t, "y", m.Nodes[1].Label)
	require.Equal(t, "z", m.Nodes[2].SourceID)
	require.Equal(t, "z", m.Nodes[2].Description)
	require.Len(t, m.Nodes, 4)
	require.Equal(t, []int{1, 2, 3}, m.Nodes[0].Children)
	require.Equal(t, m.Nodes[1].SourceID, m.Nodes[3].SourceID)
}

func TestParentIsTheLatestStrictlyLowerLevel(t *testing.T) {
	m, ds := resolve("mindmap\n  root\n    a\n      b\n    c\n   d\n     e\n")
	require.Empty(t, ds)
	parents := make([]int, len(m.Nodes))
	levels := make([]int, len(m.Nodes))
	for i, n := range m.Nodes {
		parents[i], levels[i] = n.Parent, n.Level
	}
	require.Equal(t, []int{NoParent, 0, 1, 0, 0, 4}, parents)
	require.Equal(t, []int{0, 2, 4, 2, 1, 3}, levels)
}

func TestIndentationJumpsAndTabsAreAccepted(t *testing.T) {
	m, ds := resolve("mindmap\n\troot\n\t\t\t\tdeep\n\t\tmid\n")
	require.Empty(t, ds)
	require.Equal(t, []int{NoParent, 0, 0}, []int{m.Nodes[0].Parent, m.Nodes[1].Parent, m.Nodes[2].Parent})
	require.Equal(t, []int{0, 3, 1}, []int{m.Nodes[0].Level, m.Nodes[1].Level, m.Nodes[2].Level})
}

func TestSecondRootIsRejectedAndDropped(t *testing.T) {
	src := "mindmap\n  root\n  other\n    kid\n"
	m, ds := resolve(src)
	require.Equal(t, []string{"mindmap/second-root"}, codes(ds))
	require.Equal(t, "node other has no parent; only one root is allowed", ds[0].Message)
	require.Equal(t, source.Span{Start: 17, End: 22}, ds[0].Span)
	require.Len(t, m.Nodes, 2)
	require.Equal(t, "kid", m.Nodes[1].Label)
	require.Equal(t, 0, m.Nodes[1].Parent)
}

func TestShallowerThanTheRootIsASecondRoot(t *testing.T) {
	_, ds := resolve("mindmap\n    root\n  other\n")
	require.Equal(t, []string{"mindmap/second-root"}, codes(ds))
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func TestDecorationsAttachToTheLastInsertedNode(t *testing.T) {
	m, ds := resolve("mindmap\n  root\n    a\n  ::icon(first)\n      :::one\n    b\n::icon(second)\n  :::two\n")
	require.Empty(t, ds)
	require.Equal(t, "", m.Nodes[0].Icon)
	require.Equal(t, "first", m.Nodes[1].Icon)
	require.Equal(t, "one", m.Nodes[1].Class)
	require.Equal(t, "second", m.Nodes[2].Icon)
	require.Equal(t, "two", m.Nodes[2].Class)
	require.Equal(t, []int{1, 2}, m.Nodes[0].Children)
}

func TestLaterDecorationReplacesEarlierOne(t *testing.T) {
	m, ds := resolve("mindmap\n  root\n  ::icon(a)\n  ::icon(b)\n  :::x\n  :::y z\n")
	require.Empty(t, ds)
	require.Equal(t, "b", m.Nodes[0].Icon)
	require.Equal(t, "y z", m.Nodes[0].Class)
}

func TestDecorationBeforeAnyNodeIsReported(t *testing.T) {
	src := "mindmap\n  ::icon(a)\n  :::x\n  root\n"
	m, ds := resolve(src)
	require.Equal(t, []string{"mindmap/decoration-target-missing", "mindmap/decoration-target-missing"}, codes(ds))
	require.Equal(t, "decoration has no preceding node", ds[0].Message)
	require.Equal(t, "::icon(a)", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, ":::x", src[ds[1].Span.Start:ds[1].Span.End])
	require.Equal(t, "root", m.Nodes[0].Label)
}

func TestEmptyMindmapHasNoNodes(t *testing.T) {
	m, ds := resolve("mindmap\n\n")
	require.Empty(t, ds)
	require.Empty(t, m.Nodes)
}

func TestLabelsDecodeEntitiesAndNormalizeNewlines(t *testing.T) {
	m, ds := resolve("mindmap\r\n  root((A#amp;B #9731; #nope;\r\nC))\r\n  ::icon(x\r\ny)\r\n")
	require.Empty(t, ds)
	require.Equal(t, "A&B \u2603 #nope;\nC", m.Nodes[0].Label)
	require.Equal(t, "A#amp;B #9731; #nope;\nC", m.Nodes[0].Description)
	require.Equal(t, "x\ny", m.Nodes[0].Icon)
}

func TestMarkdownDescriptionIsFlagged(t *testing.T) {
	m, ds := resolve("mindmap\n  a[\"`**b**`\"]\n")
	require.Empty(t, ds)
	require.True(t, m.Nodes[0].Markdown)
	require.Equal(t, "**b**", m.Nodes[0].Label)
	m, _ = resolve("mindmap\n  a[\"b\"]\n")
	require.False(t, m.Nodes[0].Markdown)
}

func TestConfigReadsPaddingAndMaxNodeWidthFromBothBlocks(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  mindmap:\n    padding: 12\n    maxNodeWidth: 300\n---\n%%{init: {\"mindmap\": {\"padding\": 20}}}%%\nmindmap\n  root\n")
	require.Empty(t, ds)
	require.Equal(t, Config{Padding: 20, PaddingSet: true, MaxNodeWidth: 300, MaxNodeWidthSet: true}, m.Config)
	m, _ = resolve("---\nconfig:\n  mindmap:\n    padding: 1.5\n    maxNodeWidth: -3\n    other: 4\n---\nmindmap\n  root\n")
	require.Equal(t, Config{}, m.Config)
}
