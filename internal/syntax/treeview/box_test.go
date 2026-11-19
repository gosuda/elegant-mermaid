package treeview

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func names(tv *TreeView) []string {
	out := make([]string, len(tv.Nodes))
	for i, n := range tv.Nodes {
		out[i] = n.Name.Value
	}
	return out
}

func levels(tv *TreeView) []int {
	out := make([]int, len(tv.Nodes))
	for i, n := range tv.Nodes {
		if n.Indent != nil {
			out[i] = len(n.Indent.Text)
		}
	}
	return out
}

func TestBoxInputBecomesFourSpacePerDepth(t *testing.T) {
	src := "treeView-beta\n├── a\n│   ├── b\n│   │   └── c\n│   └── d\n└── e\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []string{"a", "b", "c", "d", "e"}, names(tv))
	require.Equal(t, []int{4, 8, 12, 8, 4}, levels(tv))
}

func TestBoxSegmentWidthComesFromFirstBranchAfterColumnZero(t *testing.T) {
	src := "treeView-beta\n  ├── a\n  │   └── b\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []int{8, 16}, levels(tv))
	wide := "treeView-beta\n├────── a\n│      └── b\n"
	tv, ds = parse(wide)
	require.Empty(t, ds)
	require.Equal(t, []int{4, 8}, levels(tv))
}

func TestBoxHeavyVariantsAndTabs(t *testing.T) {
	tv, ds := parse("treeView-beta\n┣━━ a\n┃   ┗━━ b\n\t├── c\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a", "b", "c"}, names(tv))
	require.Equal(t, []int{4, 8, 8}, levels(tv))
}

func TestBoxRemovesDashesAndSpacesNotInnerText(t *testing.T) {
	tv, ds := parse("treeView-beta\n└─ a  b  \n├──c\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a  b", "c"}, names(tv))
}

func TestBoxPassesAnnotationsAndMetadata(t *testing.T) {
	src := "treeView-beta\n title T\n├── a ## d\n└── \"q\" icon(x)\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "T", tv.Title.Value)
	require.Equal(t, "d", tv.Nodes[0].Desc.Value)
	require.Equal(t, "q", tv.Nodes[1].Name.Value)
	require.Equal(t, "x", tv.Nodes[1].Icon.Value)
}

func TestBoxDecorationOnlyLinesAreOmitted(t *testing.T) {
	tv, ds := parse("treeView-beta\n│\n├── a\n│   \n ─ │ \n└── b\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a", "b"}, names(tv))
}

func TestBoxLineWithBoxCharsButNoBranchIsARoot(t *testing.T) {
	tv, ds := parse("treeView-beta\nSection ─ A.txt\n├── b\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"Section ─ A.txt", "b"}, names(tv))
	require.Equal(t, []int{0, 4}, levels(tv))
}

func TestBoxEmptyNodeSpansPrefixToLineEnd(t *testing.T) {
	src := "treeView-beta\n├── a\n└──\n"
	tv, ds := parse(src)
	require.Equal(t, []string{codeEmptyBox}, codes(ds))
	require.Equal(t, "└──", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, msgEmptyBox, ds[0].Message)
	require.Equal(t, []string{"a"}, names(tv))
}

func TestBoxMixedIndentationSpansLeadingBlanks(t *testing.T) {
	src := "treeView-beta\n├── a\n   b\n"
	tv, ds := parse(src)
	require.Equal(t, []string{codeMixed}, codes(ds))
	require.Equal(t, "   ", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, msgMixed, ds[0].Message)
	require.Equal(t, []string{"a"}, names(tv))
}

func TestBoxMixedIndentationExpandsTabs(t *testing.T) {
	src := "treeView-beta\n├── a\n\tb\n"
	_, ds := parse(src)
	require.Equal(t, []string{codeMixed}, codes(ds))
	require.Equal(t, "\t", src[ds[0].Span.Start:ds[0].Span.End])
}

func TestBoxIndentedLineBeforeFirstBranchIsMixed(t *testing.T) {
	_, ds := parse("treeView-beta\n  a\n├── b\n")
	require.Equal(t, []string{codeMixed}, codes(ds))
}

func TestBoxModeNeedsHeaderLineAlone(t *testing.T) {
	tv, _ := parse("treeView-beta  \n├── a\n")
	require.Empty(t, tv.Nodes)
}

func TestBoxSpansPointIntoOriginalLines(t *testing.T) {
	src := "treeView-beta\n├── a\n│   └── bb\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "bb", slice(src, &tv.Nodes[1].Name))
	require.Equal(t, "a", slice(src, &tv.Nodes[0].Name))
	require.Equal(t, "a", src[tv.Nodes[0].Span.End-1:tv.Nodes[0].Span.End])
}

func TestPlainInputWithoutBoxCharactersIsUnchanged(t *testing.T) {
	tv, ds := parse("treeView-beta\n  src/\n      a\n")
	require.Empty(t, ds)
	require.Equal(t, []int{2, 6}, levels(tv))
}
