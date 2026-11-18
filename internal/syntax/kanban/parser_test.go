package kanban

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func preprocessRemoved(src []byte) []source.Span { return syntax.Preprocess(src).Removed }

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

func firstStatement(start *Start) Statement {
	for _, item := range start.Document.Items {
		if item.Statement.Node != nil {
			return item.Statement
		}
	}
	return Statement{}
}

func slice(src string, span source.Span) string { return src[span.Start:span.End] }

func TestLexerSplitsColumnsCardsAndSeparators(t *testing.T) {
	require.Equal(t, []string{"KANBAN", "NL", "SPACELIST", "NODE_ID", "NL", "EOF", "END"}, tokenKinds("kanban\n  root"))
	require.Equal(t, []string{"KANBAN", "SPACELINE", "EOF", "END"}, tokenKinds("kanban\n"))
	require.Equal(t, []string{"KANBAN", "SPACELINE", "SPACELIST", "NODE_ID", "NL", "EOF", "END"}, tokenKinds("kanban  \n  root"))
	require.Equal(t, []string{"KANBAN", "NL", "SPACELIST", "NODE_ID", "NODE_DSTART", "NODE_DESCR", "NODE_DEND", "NL", "EOF", "END"}, tokenKinds("kanban\n  id[Todo]"))
}

func TestHeaderFoldsCaseAndStopsAtWordBoundary(t *testing.T) {
	require.Equal(t, "KANBAN", tokenKinds("KanBan\n")[0])
	require.Equal(t, []string{"NODE_ID", "NL", "EOF", "END"}, tokenKinds("kanbans"))
	require.Equal(t, []string{"KANBAN", "NODE_ID", "NL", "EOF", "END"}, tokenKinds("kanban-x"))
}

func TestShapeDataTokensKeepValuesAndSourceSpans(t *testing.T) {
	src := "kanban\n  a[b]@{ ticket: X }\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	statement := firstStatement(start)
	require.NotNil(t, statement.Data)
	require.Equal(t, "@{ ticket: X }", slice(src, statement.Data.Span))
	require.Equal(t, " ticket: X ", statement.Data.Value())
	require.Equal(t, "", statement.Data.Tokens[0].Text)
	require.Equal(t, "@{", slice(src, statement.Data.Tokens[0].Span))
	require.Equal(t, "  a[b]@{ ticket: X }", slice(src, statement.Span))
	require.Equal(t, []string{"KANBAN", "NL", "SPACELIST", "NODE_ID", "NODE_DSTART", "NODE_DESCR", "NODE_DEND", "SHAPE_DATA", "SHAPE_DATA", "SPACELINE", "EOF", "END"}, tokenKinds(src))
}

func TestShapeDataEmptyBracesAreDefined(t *testing.T) {
	src := "kanban\n  a@{}\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	statement := firstStatement(start)
	require.Equal(t, "a", statement.Node.ID.Text)
	require.NotNil(t, statement.Data)
	require.Equal(t, "", statement.Data.Value())
	require.Equal(t, "@{}", slice(src, statement.Data.Span))
}

func TestShapeDataQuotedLineBreaksBecomeBr(t *testing.T) {
	src := "kanban\n  a[b]@{ label: \"x\n     y\n\n z\", n: 1 }\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, " label: \"x<br/>y<br/>z\", n: 1 ", firstStatement(start).Data.Value())
	crlf, ds := parse("kanban\r\n  a[b]@{ label: \"x\r\n  y\" }\r\n")
	require.Empty(t, ds)
	require.Equal(t, " label: \"x<br/>y\" ", firstStatement(crlf).Data.Value())
}

func TestShapeDataBracesInsideQuotesDoNotClose(t *testing.T) {
	src := "kanban\n  a@{ label: \"}\" }\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, " label: \"}\" ", firstStatement(start).Data.Value())
	require.Equal(t, "@{ label: \"}\" }", slice(src, firstStatement(start).Data.Span))
}

func TestShapeDataBlocksConcatenate(t *testing.T) {
	start, ds := parse("kanban\n  a@{ x: 1 }@{ y: 2 }\n")
	require.Empty(t, ds)
	require.Equal(t, " x: 1  y: 2 ", firstStatement(start).Data.Value())
}

func TestShapeDataMultilineBlock(t *testing.T) {
	src := "kanban\n  a[b]@{\n    ticket: 1\n    assigned: z\n  }\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "\n    ticket: 1\n    assigned: z\n  ", firstStatement(start).Data.Value())
	require.Equal(t, "  a[b]@{\n    ticket: 1\n    assigned: z\n  }", slice(src, firstStatement(start).Span))
}

func TestShapeDataCaretIsLexicalError(t *testing.T) {
	_, ds := parse("kanban\n  a@{ x: ^ }\n")
	require.Equal(t, []string{"kanban/unexpected-token"}, codes(ds))
	require.Equal(t, "unexpected ^, expected one of: EOF, NL, SHAPE_DATA, SPACELINE", ds[0].Message)
	require.Equal(t, 1, ds[0].Span.End-ds[0].Span.Start)
}

func TestAtSignOutsideMetadataIsNotAnIdentifierCharacter(t *testing.T) {
	_, ds := parse("kanban\n  a@b\n")
	require.Equal(t, []string{"unexpected @, expected one of: EOF, NL, SHAPE_DATA, SPACELINE"}, messages(ds))
	_, ds = parse("kanban\n@{ x }\n")
	require.Equal(t, []string{"kanban/unknown-statement"}, codes(ds))
	require.Equal(t, "unknown statement @{", ds[0].Message)
}

func TestMetadataAfterDecorationIsRejected(t *testing.T) {
	_, ds := parse("kanban\n  a\n  ::icon(x)@{ y: 1 }\n")
	require.Equal(t, []string{"kanban/unexpected-token"}, codes(ds))
	require.Equal(t, "unexpected @{, expected one of: EOF, NL, SPACELINE", ds[0].Message)
}

func TestUnterminatedMetadataReportsOpener(t *testing.T) {
	src := "kanban\n  a[b]@{ x: 1"
	_, ds := parse(src)
	require.Equal(t, []string{"kanban/unterminated"}, codes(ds))
	require.Equal(t, "unterminated @{", ds[0].Message)
	require.Equal(t, "@{ x: 1", slice(src, ds[0].Span))
	src = "kanban\n  a@{ x: \"open"
	_, ds = parse(src)
	require.Equal(t, []string{"kanban/unterminated"}, codes(ds))
	require.Equal(t, "@{ x: \"open", slice(src, ds[0].Span))
}

func TestUnterminatedNodeIconAndMarkdown(t *testing.T) {
	for src, want := range map[string]string{
		"kanban\n  a[b":          "[b",
		"kanban\n  a[\"b":        "\"b",
		"kanban\n  a[\"`b":       "\"`b",
		"kanban\n  a\n  ::icon(": "::icon(",
	} {
		_, ds := parse(src)
		require.Equal(t, []string{"kanban/unterminated"}, codes(ds), src)
		require.Equal(t, want, slice(src, ds[0].Span), src)
	}
}

func TestInlineDecorationsStayNodeText(t *testing.T) {
	start, ds := parse("kanban\n  root ::icon(x)\n")
	require.Empty(t, ds)
	node := firstStatement(start).Node
	require.Equal(t, "root ::icon", node.ID.Text)
	require.Equal(t, "x", node.Descr.Text)
}

func TestNodeIDKeepsTrailingSpaces(t *testing.T) {
	start, ds := parse("kanban\n  id1   @{ x: 1 }\n")
	require.Empty(t, ds)
	require.Equal(t, "id1   ", firstStatement(start).Node.ID.Text)
}

func TestDecorationsAndIndent(t *testing.T) {
	start, ds := parse("kanban\n  col[Todo]\n    ::icon(fa fa-book)\n    :::urgent big\n")
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
	require.Equal(t, "fa fa-book", icon.Text)
	require.Equal(t, "urgent big", class.Text)
}

func TestSemicolonIsOrdinaryNodeText(t *testing.T) {
	start, ds := parse("kanban\n  a;b[c;d]\n")
	require.Empty(t, ds)
	node := firstStatement(start).Node
	require.Equal(t, "a;b", node.ID.Text)
	require.Equal(t, "c;d", node.Descr.Text)
}

func TestRecoveryResumesAtNextLine(t *testing.T) {
	src := "kanban\n  a[b]c\n  d[e]\n"
	start, ds := parse(src)
	require.Equal(t, []string{"kanban/unexpected-token"}, codes(ds))
	var ids []string
	for _, item := range start.Document.Items {
		if item.Statement.Node != nil && item.Statement.Node.ID != nil {
			ids = append(ids, item.Statement.Node.ID.Text)
		}
	}
	require.Contains(t, ids, "d")
}

func TestEmptyDelimiterLabelHasNoProduction(t *testing.T) {
	_, ds := parse("kanban\n  a[\"\"]\n")
	require.Equal(t, []string{"kanban/unexpected-token"}, codes(ds))
	require.Equal(t, "unexpected ], expected one of: NODE_DESCR", ds[0].Message)
}

func TestMissingHeader(t *testing.T) {
	_, ds := parse("  a\n")
	require.Equal(t, []string{"kanban/unexpected-token"}, codes(ds))
}

func TestSpansStayInsideSource(t *testing.T) {
	for _, src := range []string{
		"kanban\n  a[b]@{ x: \"\u00e9\n y\" }\n  ::icon(\u00e9)\n",
		"kanban\n\u00a0\u00a0a@{\u00e9",
		"kanban\n  a@{ \u00e9^ }\n",
	} {
		start, ds := parse(src)
		for _, d := range ds {
			require.LessOrEqual(t, d.Span.Start, d.Span.End)
			require.LessOrEqual(t, d.Span.End, len(src))
		}
		for _, item := range start.Document.Items {
			require.LessOrEqual(t, item.Statement.Span.End, len(src))
		}
	}
}

func TestCorpusParsesWithoutDiagnostics(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "kanban", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		_, ds := Parse(src, preprocessRemoved(src))
		require.Empty(t, ds, path)
	}
}
