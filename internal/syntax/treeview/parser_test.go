package treeview

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func parse(src string) (*TreeView, []diag.Diagnostic) {
	return Parse([]byte(src), syntax.Preprocess([]byte(src)).Removed)
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func slice(src string, token *Token) string {
	if token == nil {
		return "<nil>"
	}
	return src[token.Span.Start:token.Span.End]
}

type summary struct {
	indent, name, class, icon, desc string
}

func summarize(src string, tv *TreeView) []summary {
	out := make([]summary, len(tv.Nodes))
	for i, n := range tv.Nodes {
		out[i] = summary{slice(src, n.Indent), n.Name.Value, "", "", ""}
		if n.Class != nil {
			out[i].class = n.Class.Value
		}
		if n.Icon != nil {
			out[i].icon = n.Icon.Value
		}
		if n.Desc != nil {
			out[i].desc = n.Desc.Value
		}
	}
	return out
}

func TestNodeLineSplitsNameAndAnnotations(t *testing.T) {
	src := "treeView-beta\n  App.tsx :::highlight icon(logos:react) ## main component\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []summary{{"  ", "App.tsx", "highlight", "logos:react", "main component"}}, summarize(src, tv))
	require.Equal(t, "App.tsx :::highlight icon(logos:react) ## main component", src[tv.Nodes[0].Span.Start+2:tv.Nodes[0].Span.End])
}

func TestBareNameKeepsInnerBlanksAndQuotes(t *testing.T) {
	src := "treeView-beta\na b  c \"d\" 'e  \n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "a b  c \"d\" 'e", tv.Nodes[0].Name.Value)
	require.Equal(t, "a b  c \"d\" 'e  ", slice(src, &tv.Nodes[0].Name))
}

func TestDescriptionConsumesApparentAnnotations(t *testing.T) {
	tv, ds := parse("treeView-beta\n a ## d :::x icon(y)\n")
	require.Empty(t, ds)
	require.Equal(t, "d :::x icon(y)", tv.Nodes[0].Desc.Value)
	require.Nil(t, tv.Nodes[0].Class)
	require.Nil(t, tv.Nodes[0].Icon)
}

func TestRepeatedAnnotationKeepsLast(t *testing.T) {
	src := "treeView-beta\n a :::x :::y icon(p) icon(q) ## 1 \n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "y", tv.Nodes[0].Class.Value)
	require.Equal(t, "q", tv.Nodes[0].Icon.Value)
	require.Equal(t, "1", tv.Nodes[0].Desc.Value)
}

func TestAnnotationWithoutLeadingBlankIsNamePart(t *testing.T) {
	for src, name := range map[string]string{
		"a:::x":  "a:::x",
		"a## d":  "a## d",
		"a :::9": "a :::9",
	} {
		tv, ds := parse("treeView-beta\n " + src + "\n")
		require.Empty(t, ds, src)
		require.Equal(t, name, tv.Nodes[0].Name.Value, src)
		require.Nil(t, tv.Nodes[0].Class, src)
	}
}

func TestBrokenIconOpenerIsRejected(t *testing.T) {
	for _, src := range []string{"a icon(", "a icon(p", "a icon(p:)", "a icon(a b)"} {
		tv, ds := parse("treeView-beta\n " + src + "\n")
		require.NotEmpty(t, ds, src)
		require.Contains(t, codes(ds), codeUnknown, src)
		require.Nil(t, tv.Nodes[0].Icon, src)
	}
}

func TestIconValueForms(t *testing.T) {
	for src, want := range map[string]string{"icon()": "", "icon(a-b)": "a-b", "icon(p:q)": "p:q", "icon(:q)": ":q"} {
		tv, ds := parse("treeView-beta\n a " + src + "\n")
		require.Empty(t, ds, src)
		require.Equal(t, want, tv.Nodes[0].Icon.Value, src)
	}
}

func TestQuotedNameStripsQuotesAndMaySpanLines(t *testing.T) {
	src := "treeView-beta\n \"a\n b\" 'c'\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []string{"a\n b", "c"}, []string{tv.Nodes[0].Name.Value, tv.Nodes[1].Name.Value})
}

func TestBackslashDoesNotEscapeTheQuote(t *testing.T) {
	tv, ds := parse("treeView-beta\n \"a\\\" b\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"a\\", "b"}, names(tv))
}

func TestMetadataBeforeNodes(t *testing.T) {
	tv, ds := parse("treeView-beta\n title  Hello   there \n accTitle : T\n accDescr: D\n accDescr {\n x\n\n  y \n }\n a\n")
	require.Empty(t, ds)
	require.Equal(t, "Hello there", tv.Title.Value)
	require.Equal(t, "T", tv.AccTitle.Value)
	require.Equal(t, "x\ny", tv.AccDescr.Value)
	require.Len(t, tv.Nodes, 1)
}

func TestTitleWithoutBlankSuffixIsEmptyTitleThenName(t *testing.T) {
	tv, ds := parse("treeView-beta\n title.md\n")
	require.Empty(t, ds)
	require.NotNil(t, tv.Title)
	require.Empty(t, tv.Title.Value)
	require.Equal(t, []string{".md"}, names(tv))
	require.Equal(t, []int{0}, levels(tv))
}

func TestMetadataAfterNodeIsRejected(t *testing.T) {
	src := "treeView-beta\n a\n title t\n b\n"
	tv, ds := parse(src)
	require.Equal(t, []string{codeUnexpected}, codes(ds))
	require.Equal(t, " title t", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, "unexpected  title t, expected one of: BARE_NAME, CLASS_ANNOTATION, DESC_ANNOTATION, EOF, ICON_ANNOTATION, INDENTATION, QUOTED_NAME", ds[0].Message)
	require.Len(t, tv.Nodes, 2)
}

func TestIndentationWithoutNameIsRejected(t *testing.T) {
	src := "treeView-beta\n a\n  \n b\n"
	tv, ds := parse(src)
	require.Equal(t, []string{codeUnexpected}, codes(ds))
	require.Contains(t, ds[0].Message, ", expected one of: BARE_NAME, QUOTED_NAME")
	require.Len(t, tv.Nodes, 1)
}

func TestAnnotationLineAttachesToThePrecedingNode(t *testing.T) {
	tv, ds := parse("treeView-beta\n a\n :::x\n ## d\n")
	require.Empty(t, ds)
	require.Equal(t, "x", tv.Nodes[0].Class.Value)
	require.Equal(t, "d", tv.Nodes[0].Desc.Value)
}

func TestAnnotationBeforeAnyNodeIsRejected(t *testing.T) {
	_, ds := parse("treeView-beta\n ## d\n")
	require.Equal(t, []string{codeUnexpected}, codes(ds))
}

func TestHeaderMustBeAlone(t *testing.T) {
	for _, src := range []string{"treeView-beta x\n a", "treeView-betax\n a", "treeView-beta  \n a"} {
		tv, ds := parse(src)
		require.Equal(t, []string{codeUnexpected}, codes(ds), src)
		require.Empty(t, tv.Nodes, src)
	}
}

func TestUnterminatedQuoteSpansToEnd(t *testing.T) {
	src := "treeView-beta\n a\n \"never\n closed"
	tv, ds := parse(src)
	require.Equal(t, []string{codeUnterminated}, codes(ds))
	require.Equal(t, "\"never\n closed", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, "unterminated \"", ds[0].Message)
	require.Len(t, tv.Nodes, 1)
}

func TestUnclosedAccessibilityBlockIsAName(t *testing.T) {
	tv, ds := parse("treeView-beta\naccDescr {\nopen\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"accDescr {", "open"}, names(tv))
}

func TestTextAfterQuotedNameWithoutBlankIsUnknownStatement(t *testing.T) {
	src := "treeView-beta\n \"a\":::x\n b\n"
	tv, ds := parse(src)
	require.Equal(t, []string{codeUnknown}, codes(ds))
	require.Equal(t, ":::x", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, "unknown statement :", ds[0].Message)
	require.Equal(t, "b", tv.Nodes[len(tv.Nodes)-1].Name.Value)
}

func TestHiddenCommentsAndBlankLinesCreateNoNodes(t *testing.T) {
	src := "%% top\ntreeView-beta\n\n  %% inner\n a %% not a comment\n\n b\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []string{"a %% not a comment", "b"}, names(tv))
}

func TestHeaderBeforeCommentTextIsRejected(t *testing.T) {
	_, ds := parse("treeView-beta %% tail\n a\n")
	require.Equal(t, []string{codeUnexpected}, codes(ds))
}

func TestLineEndingsAreAllBreaks(t *testing.T) {
	tv, ds := parse("treeView-beta\r\n a\r\n\tb\r c\n")
	require.Empty(t, ds)
	require.Len(t, tv.Nodes, 3)
	require.Equal(t, "\t", tv.Nodes[1].Indent.Text)
}

func TestSpansUseOriginalSourceAfterFrontmatter(t *testing.T) {
	src := "---\nconfig:\n  treeView:\n    rowIndent: 3\n---\ntreeView-beta\n  a ## d\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "treeView-beta", slice(src, &tv.Header))
	require.Equal(t, "a", slice(src, &tv.Nodes[0].Name))
	require.Equal(t, " ## d", slice(src, tv.Nodes[0].Desc))
}

func TestEmptyBodyIsAccepted(t *testing.T) {
	for _, src := range []string{"treeView-beta", "treeView-beta\n", "treeView-beta\n\n%% c\n"} {
		tv, ds := parse(src)
		require.Empty(t, ds, src)
		require.Empty(t, tv.Nodes, src)
	}
}

func TestNameBytesAreNotSplitMidRune(t *testing.T) {
	src := "treeView-beta\n 🚀 rocket/ ## ünï\n"
	tv, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "🚀 rocket/", tv.Nodes[0].Name.Value)
	require.Equal(t, "ünï", tv.Nodes[0].Desc.Value)
}
