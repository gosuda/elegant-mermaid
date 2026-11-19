package treeview

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/treeview"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	pre := syntax.Preprocess([]byte(src))
	tv, parsed := syn.Parse([]byte(src), pre.Removed)
	m, resolved := Resolve([]byte(src), tv)
	return m, append(parsed, resolved...)
}

func outline(m *Model) []string {
	out := make([]string, 0, len(m.Nodes)-1)
	for _, n := range m.Nodes[1:] {
		out = append(out, strings.Repeat(".", n.Depth-1)+n.Name)
	}
	return out
}

func TestSyntheticRootHoldsTopLevelNodes(t *testing.T) {
	m, ds := resolve("treeView-beta\n a\n b\n")
	require.Empty(t, ds)
	require.Equal(t, RootLevel, m.Nodes[0].Level)
	require.Equal(t, RootName, m.Nodes[0].Name)
	require.True(t, m.Nodes[0].Directory)
	require.Equal(t, []int{1, 2}, m.Nodes[0].Children)
	require.Equal(t, NoParent, m.Nodes[0].Parent)
	require.Equal(t, []string{"a", "b"}, outline(m))
}

func TestParentIsNearestEarlierNodeWithSmallerLevel(t *testing.T) {
	m, ds := resolve("treeView-beta\n a\n    b\n  c\n d\n   e\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a", ".b", ".c", "d", ".e"}, outline(m))
	require.Equal(t, 1, m.Nodes[3].Parent)
	require.Equal(t, 4, m.Nodes[5].Parent)
}

func TestEqualLevelMakesSiblingsAndJumpsMakeChildren(t *testing.T) {
	m, ds := resolve("treeView-beta\n a\n b\n          c\n d\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a", "b", ".c", "d"}, outline(m))
}

func TestFileIsAllowedAsParent(t *testing.T) {
	m, ds := resolve("treeView-beta\n a.txt\n  b\n")
	require.Empty(t, ds)
	require.False(t, m.Nodes[1].Directory)
	require.Equal(t, 1, m.Nodes[2].Parent)
}

func TestTabCountsAsOneColumn(t *testing.T) {
	m, ds := resolve("treeView-beta\n a\n\t\tb\n \tc\n")
	require.Empty(t, ds)
	require.Equal(t, []int{1, 2, 2}, []int{m.Nodes[1].Level, m.Nodes[2].Level, m.Nodes[3].Level})
	require.Equal(t, []string{"a", ".b", ".c"}, outline(m))
}

func TestFirstLevelBelowRootIsRelativeToNothing(t *testing.T) {
	m, ds := resolve("treeView-beta\n    a\n  b\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a", "b"}, outline(m))
}

func TestTrailingSlashMakesOneDirectoryAndLosesOneSlash(t *testing.T) {
	m, ds := resolve("treeView-beta\n a/\n b//\n /\n \"c/\"\n d\n")
	require.Empty(t, ds)
	got := make([]string, 0, 5)
	for _, n := range m.Nodes[1:] {
		kind := "f"
		if n.Directory {
			kind = "d"
		}
		got = append(got, kind+":"+n.Name)
	}
	require.Equal(t, []string{"d:a", "d:b/", "d:", "d:c", "f:d"}, got)
}

func TestDuplicateNamesStayDistinct(t *testing.T) {
	m, ds := resolve("treeView-beta\n a\n a\n")
	require.Empty(t, ds)
	require.Len(t, m.Nodes, 3)
	require.NotEqual(t, m.Nodes[1].Index, m.Nodes[2].Index)
}

func TestAnnotationFields(t *testing.T) {
	m, ds := resolve("treeView-beta\n a :::hl icon(p:q) ## note \n b icon()\n c\n d ##\n")
	require.Empty(t, ds)
	a, b, c, d := m.Nodes[1], m.Nodes[2], m.Nodes[3], m.Nodes[4]
	require.Equal(t, []string{"hl", "p:q", "note"}, []string{a.Class, a.Icon, a.Description})
	require.Equal(t, IconNone, b.Icon)
	require.Empty(t, c.Icon)
	require.Empty(t, c.Class)
	require.Empty(t, d.Description)
}

func TestMetadataPopulatesTitleAndAccessibility(t *testing.T) {
	m, ds := resolve("treeView-beta\n title T\n accTitle: AT\n accDescr: AD\n a\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"T", "AT", "AD"}, []string{m.Title, m.AccTitle, m.AccDescr})
}

func TestConfigReadsHonouredKeysInThousandths(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  treeView:\n    rowIndent: 80\n    lineThickness: 2.5\n    paddingX: -1\n    showIcons: true\n---\ntreeView-beta\n a\n")
	require.Empty(t, ds)
	require.Equal(t, Length{Thousandths: 80000, Set: true}, m.Config.RowIndent)
	require.Equal(t, Length{Thousandths: 2500, Set: true}, m.Config.LineThickness)
	require.False(t, m.Config.PaddingX.Set)
	require.False(t, m.Config.PaddingY.Set)
}

func TestInitDirectiveOverridesFrontmatter(t *testing.T) {
	m, ds := resolve("---\nconfig:\n  treeView:\n    rowIndent: 1\n---\n%%{init: {\"treeView\": {\"rowIndent\": 7}}}%%\ntreeView-beta\n a\n")
	require.Empty(t, ds)
	require.Equal(t, int32(7000), m.Config.RowIndent.Thousandths)
}

func TestNestingBeyondSixtyFourIsReportedOnce(t *testing.T) {
	var b strings.Builder
	b.WriteString("treeView-beta\n")
	for i := range 70 {
		b.WriteString(strings.Repeat(" ", i+1) + "n\n")
	}
	_, ds := resolve(b.String())
	require.Len(t, ds, 1)
	require.Equal(t, "limit/nesting-depth", ds[0].Code)
	require.Equal(t, "nesting depth exceeds 64", ds[0].Message)
	require.Equal(t, "Reduce the nesting to 64 levels or fewer.", ds[0].Help)
}

func TestSixtyFourLevelsAreAccepted(t *testing.T) {
	var b strings.Builder
	b.WriteString("treeView-beta\n")
	for i := range 64 {
		b.WriteString(strings.Repeat(" ", i+1) + "n\n")
	}
	_, ds := resolve(b.String())
	require.Empty(t, ds)
}

func TestEmptyBodyHasOnlyTheRoot(t *testing.T) {
	m, ds := resolve("treeView-beta\n")
	require.Empty(t, ds)
	require.Len(t, m.Nodes, 1)
}
