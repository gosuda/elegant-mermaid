package block

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/block"
)

func resolveSource(src string) (*Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	document, _ := syn.Parse([]byte(src), prep.Removed)
	return Resolve([]byte(src), document)
}

func ids(blocks []*Block) []string {
	out := make([]string, len(blocks))
	for i, b := range blocks {
		out[i] = b.ID
	}
	return out
}

func TestColumnsAndSpans(t *testing.T) {
	m, ds := resolveSource("block-beta\ncolumns 3\nA B:2 C\n")
	require.Empty(t, ds)
	require.Equal(t, int32(3), m.Root.Columns)
	require.Equal(t, []string{"A", "B", "C"}, ids(m.Root.Children))
	require.Equal(t, []int32{1, 2, 1}, []int32{m.Root.Children[0].Span, m.Root.Children[1].Span, m.Root.Children[2].Span})
}

func TestRootColumnsDefaultToAuto(t *testing.T) {
	m, _ := resolveSource("block-beta\nA\n")
	require.Equal(t, AutoColumns, m.Root.Columns)
}

func TestSpaceExpandsIntoSlots(t *testing.T) {
	m, ds := resolveSource("block-beta\nspace:3\nA\nspace\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"space0-0", "space0-1", "space0-2", "A", "space1-0"}, ids(m.Root.Children))
	for _, i := range []int{0, 1, 2, 4} {
		require.Equal(t, "space", m.Root.Children[i].Type)
	}
}

func TestSpaceSlotsAreCapped(t *testing.T) {
	m, _ := resolveSource("block-beta\nspace:99999999999\nspace:5\nA\n")
	require.Equal(t, maxSpaceSlots+1, len(m.Root.Children))
	require.Equal(t, "space", m.Root.Children[maxSpaceSlots-1].Type)
	require.Equal(t, "A", m.Root.Children[maxSpaceSlots].ID)
}

func TestCompositeBlocks(t *testing.T) {
	m, ds := resolveSource("block-beta\nblock:outer\ncolumns 2\nx y\nend\nblock\nz\nend\n")
	require.Empty(t, ds)
	outer, anonymous := m.Root.Children[0], m.Root.Children[1]
	require.Equal(t, "composite", outer.Type)
	require.Equal(t, "outer", outer.ID)
	require.Equal(t, int32(2), outer.Columns)
	require.Equal(t, []string{"x", "y"}, ids(outer.Children))
	require.Equal(t, "block0", anonymous.ID)
	require.Equal(t, []string{"z"}, ids(anonymous.Children))
}

func TestGeneratedIDsAvoidExplicitOnes(t *testing.T) {
	m, _ := resolveSource("block-beta\nblock0\nblock\nz\nend\nroot0\n")
	require.Equal(t, "root0~1", m.Root.ID)
	require.Equal(t, "block0~1", m.Root.Children[1].ID)
}

func TestShapesAndDirections(t *testing.T) {
	m, ds := resolveSource("block-beta\na[\"s\"] b(\"r\") c((\"c\")) d{\"d\"} e{{\"h\"}} f([\"t\"]) g[[\"u\"]] h[(\"y\")] i(((\"o\"))) j>\"k\"] k[/\"p\"/] l[\\\"q\"\\] m[/\"w\"\\] n[\\\"v\"/] o<[\"arr\"]>(right, down)\nplain\n")
	require.Empty(t, ds)
	var types []string
	for _, b := range m.Root.Children {
		types = append(types, b.Type)
	}
	require.Equal(t, []string{"square", "round", "circle", "diamond", "hexagon", "stadium", "subroutine", "cylinder", "doublecircle", "rect_left_inv_arrow", "lean_right", "lean_left", "trapezoid", "inv_trapezoid", "block_arrow", "na"}, types)
	require.Equal(t, []string{"right", "down"}, m.Find("o").Directions)
	require.Equal(t, "arr", m.Find("o").Label)
	require.Equal(t, "plain", m.Find("plain").Label)
}

func TestEdgeStyles(t *testing.T) {
	m, ds := resolveSource("block-beta\nA --> B\nB --- C\nC ==> D\nD -.-> E\nE --x F\nA -- \"t\" --> C\nG <--> H\n")
	require.Empty(t, ds)
	require.Len(t, m.Edges, 7)
	type shape struct{ thick, pattern, start, end, label string }
	var got []shape
	for _, e := range m.Edges {
		got = append(got, shape{e.Thickness, e.Pattern, e.ArrowStart, e.ArrowEnd, e.Label})
	}
	require.Equal(t, []shape{
		{"normal", "solid", "arrow_open", "arrow_point", ""},
		{"normal", "solid", "arrow_open", "", ""},
		{"thick", "solid", "arrow_open", "arrow_point", ""},
		{"normal", "dotted", "arrow_open", "arrow_point", ""},
		{"normal", "solid", "arrow_open", "arrow_cross", ""},
		{"normal", "solid", "arrow_open", "arrow_point", "t"},
		{"normal", "solid", "arrow_point", "arrow_point", ""},
	}, got)
}

func TestChainedEdgesLinkNeighbours(t *testing.T) {
	m, _ := resolveSource("block-beta\nA --> B --> C\n")
	require.Equal(t, [][2]string{{"A", "B"}, {"B", "C"}}, [][2]string{{m.Edges[0].Start, m.Edges[0].End}, {m.Edges[1].Start, m.Edges[1].End}})
}

func TestEdgeToCompositeKeepsEdge(t *testing.T) {
	m, _ := resolveSource("block-beta\nblock:g\nx\nend\nA --> g\n")
	require.Len(t, m.Edges, 1)
	require.Equal(t, "g", m.Edges[0].End)
}

func TestLabelEntitiesAreDecoded(t *testing.T) {
	m, _ := resolveSource("block-beta\nA[\"a #amp; b #35; #nope; #0;\"]\n")
	require.Equal(t, "a & b # #nope; #0;", m.Find("A").Label)
}

func TestSecondDeclarationRelabels(t *testing.T) {
	m, _ := resolveSource("block-beta\nA[\"one\"]\nA(\"two\")\nA\n")
	require.Len(t, m.Root.Children, 1)
	require.Equal(t, "two", m.Find("A").Label)
	require.Equal(t, "round", m.Find("A").Type)
}

func TestStyleTargetMustExist(t *testing.T) {
	m, ds := resolveSource("block-beta\nA\nstyle A fill:#f00\nstyle Z fill:#0f0\n")
	require.Equal(t, []string{"block/style-target-unknown"}, codes(ds))
	require.Equal(t, []string{"fill:#f00"}, m.Find("A").Styles)
}

func TestWidthBeyondColumnsIsReported(t *testing.T) {
	_, ds := resolveSource("block-beta\ncolumns 2\nA:3 B:2\n")
	require.Equal(t, []string{"block/width-exceeds-columns"}, codes(ds))
	require.True(t, strings.Contains(ds[0].Message, "A"))
}

func TestClassDefsAndClasses(t *testing.T) {
	m, _ := resolveSource("block-beta\nclassDef k fill:#fff,color:#000\nA B\nclass A,B k\n")
	require.Equal(t, []string{"k"}, m.Find("A").Classes)
	require.Equal(t, []string{"k"}, m.Find("B").Classes)
	require.Equal(t, []string{"fill:#fff", "color:#000"}, m.Classes[0].Styles)
	require.Equal(t, []string{"fill:#000"}, m.Classes[0].TextStyles)
}

func TestPaddingConfig(t *testing.T) {
	cases := map[string]int64{
		"---\nconfig:\n  block:\n    padding: 12\n---\nblock-beta\nA\n": 12,
		"%%{init: {\"block\": {\"padding\": 3}}}%%\nblock-beta\nA\n":    3,
	}
	for src, want := range cases {
		m, _ := resolveSource(src)
		require.Equal(t, []ConfigEntry{{Key: "padding", Value: want}}, m.Config, src)
	}
	for _, src := range []string{
		"---\nconfig:\n  block:\n    padding: 5000\n---\nblock-beta\nA\n",
		"---\nconfig:\n  block:\n    padding: -1\n---\nblock-beta\nA\n",
		"---\nconfig:\n  block:\n    padding: x\n---\nblock-beta\nA\n",
	} {
		m, _ := resolveSource(src)
		require.Empty(t, m.Config, src)
	}
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}
