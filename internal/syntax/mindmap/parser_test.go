package mindmap

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(src string) (*Start, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func tokenKinds(src string) []string {
	s := newScanner(src, nil)
	var kinds []string
	for {
		token := s.next()
		kinds = append(kinds, token.Kind)
		if token.Kind == kindEnd {
			return kinds
		}
	}
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Message
	}
	return out
}

func TestLexerAppendsVirtualNewlineAndSplitsLines(t *testing.T) {
	require.Equal(t, []string{"MINDMAP", "NL", "SPACELIST", "NODE_ID", "NL", "EOF", "END"}, tokenKinds("mindmap\n  root"))
	require.Equal(t, []string{"MINDMAP", "SPACELINE", "EOF", "END"}, tokenKinds("mindmap\n"))
	require.Equal(t, []string{"MINDMAP", "SPACELINE", "SPACELIST", "NODE_ID", "NL", "EOF", "END"}, tokenKinds("mindmap  \n  root"))
}

func TestLexerFoldsHeaderAndStopsAtWordBoundary(t *testing.T) {
	require.Equal(t, "MINDMAP", tokenKinds("MindMap\n")[0])
	require.Equal(t, []string{"NODE_ID", "NL", "EOF", "END"}, tokenKinds("mindmapper"))
	require.Equal(t, []string{"MINDMAP", "NODE_ID", "NL", "EOF", "END"}, tokenKinds("mindmap-x"))
}

func TestLexerShapeOpenersFollowSourceOrder(t *testing.T) {
	for opener, closer := range map[string]string{"-)": ")", "(-": ")", "))": ")", ")": ")", "((": "))", "{{": "}}", "(": ")", "[": "]"} {
		require.Equal(t, []string{"NODE_ID", "NODE_DSTART", "NODE_DESCR", "NODE_DEND", "NL", "EOF", "END"}, tokenKinds("a"+opener+"b"+closer), opener)
	}
	require.Equal(t, []string{"NODE_DSTART", "NODE_DESCR", "NODE_DEND", "NL", "EOF", "END"}, tokenKinds("((b))"))
}

func TestLexerNodeModeKeepsPermissiveDescriptions(t *testing.T) {
	start, ds := parse("mindmap\n  a[b\"c(d]\n")
	require.Equal(t, []string{"unexpected d], expected one of: EOF, NL, SPACELINE"}, messages(ds))
	require.Equal(t, `b"c`, firstNode(start).Descr.Text)
	start, ds = parse("mindmap\n  a[b\"c\"d]\n")
	require.Empty(t, ds)
	require.Equal(t, `b"c"d`, firstNode(start).Descr.Text)
	start, ds = parse("mindmap\n  a[line1\nline2]\n")
	require.Empty(t, ds)
	require.Equal(t, "line1\nline2", firstNode(start).Descr.Text)
}

func TestLexerRejectsBracesInInitial(t *testing.T) {
	_, ds := parse("mindmap\n{x}\n")
	require.Equal(t, []string{"mindmap/unknown-statement"}, codes(ds))
	require.Equal(t, "unknown statement {", ds[0].Message)
	_, ds = parse("mindmap\n  {x}\n")
	require.Equal(t, []string{"unexpected {, expected one of: CLASS, EOF, ICON, NL, NODE_DSTART, NODE_ID, SPACELINE"}, messages(ds))
}

func TestInlineDecorationsStayNodeText(t *testing.T) {
	start, ds := parse("mindmap\n  root ::icon(x)\n")
	require.Empty(t, ds)
	node := firstNode(start)
	require.Equal(t, "root ::icon", node.ID.Text)
	require.Equal(t, "x", node.Descr.Text)
}

func firstNode(start *Start) *Node {
	for _, item := range start.Document.Items {
		if item.Statement.Node != nil {
			return item.Statement.Node
		}
	}
	return nil
}

func TestDescriptionKinds(t *testing.T) {
	for src, want := range map[string]Description{
		"a":          DescriptionBare,
		"a[b]":       DescriptionPlain,
		"a[\"b\"]":   DescriptionQuoted,
		"a[\"`b`\"]": DescriptionMarkdown,
	} {
		start, ds := parse("mindmap\n  " + src + "\n")
		require.Empty(t, ds, src)
		require.Equal(t, want, firstNode(start).Description, src)
	}
	start, _ := parse("mindmap\n  a[`b`]\n")
	require.Equal(t, DescriptionPlain, firstNode(start).Description)
	require.Equal(t, "`b`", firstNode(start).Descr.Text)
}

func TestEmptyQuotedDescriptionInventsNoToken(t *testing.T) {
	_, ds := parse("mindmap\n  a[\"\"]\n")
	require.Equal(t, []string{"mindmap/unexpected-token"}, codes(ds))
	require.Equal(t, "unexpected ], expected one of: NODE_DESCR", ds[0].Message)
}

func TestBlankStatementsAndStops(t *testing.T) {
	start, ds := parse("mindmap\n  root\n\n  \n    a\n")
	require.Empty(t, ds)
	require.Len(t, start.Document.Items, 2)
	start, ds = parse("mindmap\n")
	require.Empty(t, ds)
	require.NotNil(t, start.Document.Items[0].Statement.Blank)
}

func TestHeaderRequiresOneNewlineBeforeIndentedStatement(t *testing.T) {
	_, ds := parse("mindmap\n\n  root\n")
	require.Equal(t, []string{"mindmap/unexpected-token"}, codes(ds))
	require.Equal(t, "unexpected   , expected one of: EOF, NL, SPACELINE", ds[0].Message)
	_, ds = parse("mindmap  \n  root\n")
	require.Equal(t, []string{"mindmap/unexpected-token"}, codes(ds))
}

func TestEmptyDocumentNeedsAStatement(t *testing.T) {
	_, ds := parse("mindmap")
	require.Equal(t, []string{"mindmap/unexpected-token"}, codes(ds))
	require.Equal(t, "unexpected end of input, expected one of: CLASS, ICON, NODE_DSTART, NODE_ID, SPACELINE, SPACELIST", ds[0].Message)
	require.Equal(t, source.Span{Start: 7, End: 7}, ds[0].Span)
}

func TestUnexpectedTokenListsAcceptedKinds(t *testing.T) {
	_, ds := parse("mindmap\n  a[b]c\n")
	require.Equal(t, []string{"unexpected c, expected one of: EOF, NL, SPACELINE"}, messages(ds))
	require.Equal(t, source.Span{Start: 14, End: 15}, ds[0].Span)
	_, ds = parse("mindmap\n  a[\n")
	require.Equal(t, []string{"mindmap/unterminated"}, codes(ds))
}

func TestRecoveryResumesAfterTheLineEnd(t *testing.T) {
	start, ds := parse("mindmap\n  root\n    a[b]c\n    d\n")
	require.Equal(t, []string{"mindmap/unexpected-token"}, codes(ds))
	var ids []string
	for _, item := range start.Document.Items {
		if item.Statement.Node != nil && item.Statement.Node.ID != nil {
			ids = append(ids, item.Statement.Node.ID.Text)
		}
	}
	require.Equal(t, []string{"root", "a", "d"}, ids)
}

func TestRecoveryContinuesThroughOpenShapesAcrossLines(t *testing.T) {
	start, ds := parse("mindmap\n  root\n    a[\"x\"y\nz]\n    d\n")
	require.Equal(t, []string{"mindmap/unexpected-token"}, codes(ds))
	last := start.Document.Items[len(start.Document.Items)-1].Statement.Node
	require.Equal(t, "d", last.ID.Text)
}

func TestUnknownStatementSpansToTheLineEnd(t *testing.T) {
	start, ds := parse("mindmap\n{x y}\n  z\n")
	require.Equal(t, []string{"mindmap/unknown-statement"}, codes(ds))
	require.Equal(t, source.Span{Start: 8, End: 13}, ds[0].Span)
	require.Equal(t, "z", firstNode(start).ID.Text)
}

func TestUnterminatedSpansOpenerToEndOfInput(t *testing.T) {
	for src, want := range map[string]struct {
		message string
		start   int
	}{
		"mindmap\n  a[b":           {"unterminated [", 11},
		"mindmap\n  a((b":          {"unterminated ((", 11},
		"mindmap\n  a[\"b":         {"unterminated \"", 12},
		"mindmap\n  a[\"`b":        {"unterminated \"`", 12},
		"mindmap\n  a\n  ::icon(x": {"unterminated ::icon(", 14},
		"mindmap\n  a\n  ::ICON(x": {"unterminated ::ICON(", 14},
	} {
		_, ds := parse(src)
		require.Len(t, ds, 1, src)
		require.Equal(t, "mindmap/unterminated", ds[0].Code, src)
		require.Equal(t, want.message, ds[0].Message, src)
		require.Equal(t, source.Span{Start: want.start, End: len(src)}, ds[0].Span, src)
	}
}

func TestClassModeAtEndOfInputIsABlankClass(t *testing.T) {
	start, ds := parse("mindmap\n  a\n  :::")
	require.Empty(t, ds)
	for _, item := range start.Document.Items {
		require.Nil(t, item.Statement.Class)
	}
}

func TestDecorationSpansIncludeDelimiters(t *testing.T) {
	src := "mindmap\n  a\n  ::icon(fa fa-book)\n  :::cls x\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	var icon, class *Token
	for _, item := range start.Document.Items {
		if item.Statement.Icon != nil {
			icon = item.Statement.Icon
		}
		if item.Statement.Class != nil {
			class = item.Statement.Class
		}
	}
	require.Equal(t, "::icon(fa fa-book)", src[icon.Span.Start:icon.Span.End])
	require.Equal(t, "fa fa-book", icon.Text)
	require.Equal(t, ":::cls x", src[class.Span.Start:class.Span.End])
	require.Equal(t, "cls x", class.Text)
}

func TestEmptyIconAndClassCreateNoDecoration(t *testing.T) {
	start, ds := parse("mindmap\n  a\n  ::icon()\n  :::\n")
	require.Empty(t, ds)
	for _, item := range start.Document.Items {
		require.Nil(t, item.Statement.Icon)
		require.Nil(t, item.Statement.Class)
	}
}

func TestCRLFAndLoneCRAreLineEnds(t *testing.T) {
	for _, src := range []string{"mindmap\r\n  root\r\n    a\r\n", "mindmap\n  root\r    a\r"} {
		start, ds := parse(src)
		require.Empty(t, ds, src)
		require.Len(t, start.Document.Items, 2, src)
		require.Equal(t, "root", start.Document.Items[0].Statement.Node.ID.Text)
	}
}

func TestRemovedSpansKeepSourceOffsets(t *testing.T) {
	src := "---\ntitle: t\n---\nmindmap\n  root\n"
	removed := []source.Span{{Start: 0, End: 17}}
	start, ds := Parse([]byte(src), removed)
	require.Empty(t, ds)
	node := firstNode(start)
	require.Equal(t, "root", src[node.Span.Start:node.Span.End])
	require.Equal(t, "mindmap", src[start.Header.Span.Start:start.Header.Span.End])
}

func TestLeadingBlankLinesPrecedeTheHeader(t *testing.T) {
	src := "\n\n  mindmap\n  root\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "mindmap", src[start.Header.Span.Start:start.Header.Span.End])
	require.Equal(t, "root", src[firstNode(start).Span.Start:firstNode(start).Span.End])
}

func TestStatementSpanExcludesTheStop(t *testing.T) {
	src := "mindmap\n  root\n    a[b]\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	statement := start.Document.Items[1].Statement
	require.Equal(t, "    a[b]", src[statement.Span.Start:statement.Span.End])
	require.Equal(t, "\n", src[start.Document.Items[1].Stop.Span.Start:start.Document.Items[1].Stop.Span.End])
}

func TestParseNeverPanicsOnHostileInput(t *testing.T) {
	for _, src := range []string{"", "mindmap", ":::", strings.Repeat("(", 50), "mindmap\n" + strings.Repeat("a[\"`", 20), "mindmap\n\x00\xff"} {
		require.NotPanics(t, func() { Parse([]byte(src), nil) }, src)
	}
}
