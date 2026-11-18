package treemap

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/treemap"
)

func resolve(src string) *Model {
	text := []byte(src)
	prep := syntax.Preprocess(text)
	tree, parsed := syn.Parse(text, prep.Removed)
	if len(parsed) > 0 {
		panic(parsed[0].Message)
	}
	m, _ := Resolve(text, tree)
	return m
}

func TestThousandths(t *testing.T) {
	for literal, want := range map[string]int64{
		"12": 12000, "0": 0, ".5": 500, "5.": 5000, "1234.5678": 1234568, "1234.5674": 1234567,
		"0.0005": 1, "0.0004": 0, "007": 7000, "1234567": 1234567000,
	} {
		require.Equal(t, want, Thousandths(literal), literal)
	}
	require.Equal(t, int64(wholeCap)*scale, Thousandths(strings.Repeat("9", 40)))
}

func TestFormatValue(t *testing.T) {
	for value, want := range map[int64]string{
		0: "0", 1000: "1", 500: "0.5", 1234: "1.234", 1234567000: "1,234,567", 1234567500: "1,234,567.5", 999000: "999",
		1000000: "1,000", 100000000: "100,000",
	} {
		require.Equal(t, want, FormatValue(value), value)
	}
}

func TestHierarchyFollowsIndentation(t *testing.T) {
	m := resolve("treemap-beta\n\"A\"\n  \"B\": 1\n  \"C\"\n    \"D\": 2\n      \"E\": 3\n\"F\"\n  \"G\": 4\n")
	require.Len(t, m.Roots, 2)
	a, f := m.Roots[0], m.Roots[1]
	require.Equal(t, "A", a.Name)
	require.Len(t, a.Children, 2)
	require.Equal(t, "B", a.Children[0].Name)
	c := a.Children[1]
	require.Equal(t, "C", c.Name)
	require.Equal(t, []string{"D", "E"}, []string{c.Children[0].Name, c.Children[1].Name})
	require.Equal(t, "F", f.Name)
	require.Equal(t, int64(4000), f.Children[0].Value)
	require.Equal(t, 7, m.Count)
}

func TestIndentationJumpsNestUnderTop(t *testing.T) {
	m := resolve("treemap-beta\n\"A\"\n      \"B\"\n   \"C\": 1\n")
	require.Len(t, m.Roots, 1)
	a := m.Roots[0]
	require.Len(t, a.Children, 2)
	require.Equal(t, "B", a.Children[0].Name)
	require.Equal(t, "C", a.Children[1].Name)
}

func TestDocumentOrderIndexes(t *testing.T) {
	m := resolve("treemap-beta\n\"A\"\n  \"B\": 1\n\"C\"\n  \"D\": 2\n")
	var order []int
	var walk func(n *Node)
	walk = func(n *Node) {
		order = append(order, n.Index)
		for _, c := range n.Children {
			walk(c)
		}
	}
	for _, r := range m.Roots {
		walk(r)
	}
	require.Equal(t, []int{0, 1, 2, 3}, order)
}

func TestInvalidNumberIsZero(t *testing.T) {
	m := resolve("treemap-beta\n\"A\"\n  \"B\": ...\n")
	leaf := m.Roots[0].Children[0]
	require.True(t, leaf.Leaf)
	require.Equal(t, int64(0), leaf.Value)
}

func TestClassStyles(t *testing.T) {
	m := resolve("treemap-beta\nclassDef big fill:red\\,x,color:blue,stroke:#fff\nclassDef big font-size,color\n\"A\":::big\n  \"B\": 1:::missing\n")
	require.Len(t, m.Classes, 1)
	require.Equal(t, []string{"fill:red,x", "color:blue", "stroke:#fff", "font-size", "color"}, m.Classes[0].Styles)
	require.Equal(t, []string{"font-size", "color"}, m.Classes[0].TextStyles)
	require.Equal(t, "big", m.Roots[0].Selector)
	require.Equal(t, m.Classes[0].Styles, m.Roots[0].Styles)
	require.Empty(t, m.Roots[0].Children[0].Styles)
}

func TestMetadataAndConfig(t *testing.T) {
	m := resolve("---\ntitle: Front\nconfig:\n  treemap:\n    padding: 20\n    nodeWidth: 50\n    other: 3\n---\n%%{init: {\"treemap\": {\"nodeHeight\": 30}}}%%\ntreemap-beta\ntitle Body\naccTitle: at\naccDescr: ad\n\"A\"\n")
	require.Equal(t, "Body", m.Title)
	require.Equal(t, "at", m.AccTitle)
	require.Equal(t, "ad", m.AccDescr)
	require.Equal(t, []ConfigEntry{{"nodeHeight", 30}, {"nodeWidth", 50}, {"padding", 20}}, m.Config)
}

func TestFrontMatterTitleWithoutBodyTitle(t *testing.T) {
	m := resolve("---\ntitle: Front\n---\ntreemap-beta\n\"A\"\n")
	require.Equal(t, "Front", m.Title)
}

func TestConfigRangesAreEnforced(t *testing.T) {
	m := resolve("---\nconfig:\n  treemap:\n    padding: -1\n    nodeWidth: 0\n    nodeHeight: 99999\n---\ntreemap-beta\n\"A\"\n")
	require.Empty(t, m.Config)
}

func TestNestingDepthDiagnostic(t *testing.T) {
	var b strings.Builder
	b.WriteString("treemap-beta\n")
	for i := range 70 {
		b.WriteString(strings.Repeat(" ", i))
		b.WriteString("\"S\"\n")
	}
	text := []byte(b.String())
	prep := syntax.Preprocess(text)
	tree, _ := syn.Parse(text, prep.Removed)
	_, ds := Resolve(text, tree)
	require.Len(t, ds, 1)
	require.Equal(t, "limit/nesting-depth", ds[0].Code)
}
