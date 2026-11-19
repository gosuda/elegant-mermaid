package architecture

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(src string) (*Architecture, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func kinds(src string) []string {
	var out []string
	for _, token := range lex(src, nil) {
		out = append(out, token.Kind)
	}
	return out
}

func TestHeaderForms(t *testing.T) {
	for _, header := range []string{"architecture-beta", "architecture"} {
		root, ds := parse(header + "\nservice a(server)\n")
		require.Empty(t, ds, header)
		require.Equal(t, header, root.Header.Kind)
		require.Len(t, root.Statements, 1)
	}
	root, ds := parse("architecture-beta service a(server)\n")
	require.Empty(t, ds)
	require.Len(t, root.Statements, 1)
}

func TestStatementForms(t *testing.T) {
	src := "architecture-beta\n" +
		"group g(cloud)[ \"Quoted \\\"title\\\"\" ] in p\n" +
		"service s \"text\" [T] in g\n" +
		"service i(logos:aws-lambda)\n" +
		"junction j in g\n" +
		"s{group}:R <-[ a b ]-> L:j{group}\n" +
		"i:B -- T:s\n" +
		"align row s i j\n"
	root, ds := parse(src)
	require.Empty(t, ds)
	require.Len(t, root.Statements, 7)

	group := root.Statements[0].Kind.(*Group)
	require.Equal(t, "g", group.ID.Text)
	require.Equal(t, "cloud", group.Icon.Text)
	require.Equal(t, `Quoted "title"`, group.Title.Text)
	require.Equal(t, "p", group.In.Text)
	require.Equal(t, `group g(cloud)[ "Quoted \"title\"" ] in p`, src[root.Statements[0].Span.Start:root.Statements[0].Span.End])

	service := root.Statements[1].Kind.(*Service)
	require.Equal(t, "text", service.IconText.Text)
	require.Nil(t, service.Icon)
	require.Equal(t, "T", service.Title.Text)
	require.Equal(t, "g", service.In.Text)

	icon := root.Statements[2].Kind.(*Service)
	require.Equal(t, "logos:aws-lambda", icon.Icon.Text)
	require.Nil(t, icon.Title)

	junction := root.Statements[3].Kind.(*Junction)
	require.Equal(t, "g", junction.In.Text)

	edge := root.Statements[4].Kind.(*Edge)
	require.Equal(t, "s", edge.LhsID.Text)
	require.NotNil(t, edge.LhsGroup)
	require.NotNil(t, edge.LhsInto)
	require.NotNil(t, edge.RhsInto)
	require.NotNil(t, edge.RhsGroup)
	require.Equal(t, "a b", edge.Title.Text)
	require.Equal(t, "R", edge.LhsDir.Text)
	require.Equal(t, "L", edge.RhsDir.Text)
	require.Equal(t, "j", edge.RhsID.Text)

	plain := root.Statements[5].Kind.(*Edge)
	require.Nil(t, plain.LhsGroup)
	require.Nil(t, plain.Title)
	require.Nil(t, plain.LhsInto)

	align := root.Statements[6].Kind.(*Alignment)
	require.Equal(t, "row", align.Direction.Text)
	require.Len(t, align.Members, 3)
	require.Equal(t, source.Span{Start: root.Statements[6].Span.Start, End: len(src) - 1}, root.Statements[6].Span)
}

func TestMetadataStatementsMerge(t *testing.T) {
	root, ds := parse("architecture-beta\ntitle  A   B\naccTitle: t %% c\naccDescr {\n a  b\n\n c\n}\nservice a(server)\ntitle second\n")
	require.Empty(t, ds)
	require.Len(t, root.Statements, 3)
	items := root.Statements[0].Kind.(*TitleAndAccessibilities).Items
	require.Len(t, items, 3)
	require.Equal(t, MetadataItem{Field: "title", Value: "A B", Span: items[0].Span}, items[0])
	require.Equal(t, "t", items[1].Value)
	require.Equal(t, "a b\nc", items[2].Value)
}

func TestPortLettersWinOverIdentifiers(t *testing.T) {
	require.Equal(t, []string{"architecture-beta", "NEWLINE", "service", "ARROW_DIRECTION", "ID", "EOF"}, kinds("architecture-beta\nservice Lambda"))
	require.Equal(t, []string{"ID", "EOF"}, kinds("left_disk"))
	require.Equal(t, []string{"ID", "EOF"}, kinds("1Leftofmid"))
	require.Equal(t, []string{"ID", "EOF"}, kinds("trueblue"))
	require.Equal(t, []string{"ID", "EOF"}, kinds("group-1"))
	require.Equal(t, []string{"group", "-", "EOF"}, kinds("group-"))
	require.Equal(t, []string{"TITLE", "ID", "EOF"}, kinds("title1"))
	require.Equal(t, []string{"ID", "EOF"}, kinds("accTitle1"))
}

func TestArrowTokens(t *testing.T) {
	require.Equal(t, []string{"ID", ":", "ARROW_DIRECTION", "ARROW_INTO", "--", "ARROW_INTO", "ARROW_DIRECTION", ":", "ID", "ARROW_GROUP", "EOF"}, kinds("a:R<-->L:b{group}"))
	require.Equal(t, []string{"-", "ARCH_TITLE", "-", "EOF"}, kinds("-[x]-"))
}

func TestTitleAndIconValues(t *testing.T) {
	for _, tc := range []struct{ in, kind, text string }{
		{`[ x ]`, "ARCH_TITLE", "x"},
		{`["x y"]`, "ARCH_TITLE", "x y"},
		{`['it\'s']`, "ARCH_TITLE", "it's"},
		{`["x]`, "ARCH_TITLE", `"x`},
		{`["a"b]`, "ARCH_TITLE", `"a"b`},
		{`[" "]`, "ARCH_TITLE", ""},
		{`(a-b:c)`, "ARCH_ICON", "a-b:c"},
		{`"a\nb"`, "STRING", "a\nb"},
		{`'q\'q'`, "STRING", "q'q"},
	} {
		tokens := lex(tc.in, nil)
		require.Equal(t, tc.kind, tokens[0].Kind, tc.in)
		require.Equal(t, tc.text, tokens[0].Text, tc.in)
		require.Equal(t, source.Span{End: len(tc.in)}, tokens[0].Span, tc.in)
	}
}

func TestUnterminatedAndInvalidDelimiters(t *testing.T) {
	for _, tc := range []struct{ src, token string }{
		{"architecture-beta\nservice a(server", "("},
		{"architecture-beta\nservice a[title", "["},
		{"architecture-beta\nservice a \"text", "\""},
		{"architecture-beta\naccDescr {\nnever", "{"},
	} {
		_, ds := parse(tc.src)
		require.Equal(t, []string{"architecture/unterminated: unterminated " + tc.token}, messages(ds), tc.src)
		require.Equal(t, len(tc.src), ds[0].Span.End, tc.src)
	}
	for _, src := range []string{"service a(a b)", "service a()", "service a[]", "service a[x\ny]", "service a[x[y]]", "service a;", "service \"a\\\n\""} {
		_, ds := parse("architecture-beta\n" + src + "\n")
		require.NotEmpty(t, ds, src)
	}
}

func marked(src string) (string, source.Span) {
	start := strings.IndexByte(src, '|')
	end := strings.LastIndexByte(src, '|') - 1
	return src[:start] + src[start+1:end+1] + src[end+2:], source.Span{Start: start, End: end}
}

func TestDiagnostics(t *testing.T) {
	for _, tc := range []struct{ src, want string }{
		{"architecture-beta\nfoo |bar|\n", "architecture/unexpected-token: unexpected bar, expected one of: :, ARROW_GROUP"},
		{"architecture-beta\n|-- x|\n", "architecture/unknown-statement: unknown statement --"},
		{"architecture-beta\nservice |L|\n", "architecture/unexpected-token: unexpected L, expected one of: ID"},
		{"architecture-beta\nservice a[x]|(y)|\n", "architecture/unexpected-token: unexpected (y), expected one of: EOF, NEWLINE, in"},
		{"architecture-beta\nservice a (x) |(y)|\n", "architecture/unexpected-token: unexpected (y), expected one of: ARCH_TITLE, EOF, NEWLINE, in"},
		{"architecture-beta\njunction j|[T]|\n", "architecture/unexpected-token: unexpected [T], expected one of: EOF, NEWLINE, in"},
		{"architecture-beta\na:|X| -- L:b\n", "architecture/invalid-direction: invalid edge direction X; expected L, R, T, B"},
		{"architecture-beta\na:R -- |l|:b\n", "architecture/invalid-direction: invalid edge direction l; expected L, R, T, B"},
		{"architecture-beta\na:R --|-| L:b\n", "architecture/unexpected-token: unexpected -, expected one of: ARROW_DIRECTION, ARROW_INTO"},
		{"architecture-beta\na:R <- |L|:b\n", "architecture/unexpected-token: unexpected L, expected one of: ARCH_TITLE"},
		{"architecture-beta\n|align row a|\n", "architecture/align-too-few-members: alignment requires at least two members"},
		{"architecture-beta\nalign |diag| a b\n", "architecture/unexpected-token: unexpected diag, expected one of: column, row"},
		{"architecture-beta\nalign row a b |:|\n", "architecture/unexpected-token: unexpected :, expected one of: EOF, ID, NEWLINE"},
		{"architecture-beta\nservice a(server) |service| b(server)\n", "architecture/unexpected-token: unexpected service, expected one of: ARCH_TITLE, EOF, NEWLINE, in"},
	} {
		src, span := marked(tc.src)
		_, ds := parse(src)
		require.Equal(t, []string{tc.want}, messages(ds), src)
		require.Equal(t, span, ds[0].Span, src)
	}
}

func TestRecoveryContinuesOnTheNextLine(t *testing.T) {
	root, ds := parse("architecture-beta\nservice a(server)\nservice (x)\nservice b(server)\n")
	require.Len(t, ds, 1)
	require.Len(t, root.Statements, 2)
}

func TestRemovedSpansAreSkipped(t *testing.T) {
	src := "architecture-beta\n%%{init}%%\nservice a(server)\n"
	root, ds := Parse([]byte(src), []source.Span{{Start: 18, End: 28}})
	require.Empty(t, ds)
	require.Len(t, root.Statements, 1)
}

func TestRootSpansTheDocument(t *testing.T) {
	src := "\n\narchitecture-beta\nservice a(server)\n"
	root, _ := parse(src)
	require.Equal(t, source.Span{Start: 2, End: len(src)}, root.Span)
}
