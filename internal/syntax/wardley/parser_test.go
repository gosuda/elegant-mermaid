package wardley

import (
	"os"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func parse(src string) (*Wardley, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	return Parse([]byte(src), prep.Removed)
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
	for _, t := range lex(src, nil) {
		out = append(out, t.Kind)
	}
	return out
}

func TestCorpusParsesWithoutDiagnostics(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "wardley", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		_, ds := parse(string(src))
		require.Empty(t, messages(ds), path)
	}
}

func TestStatementFamilies(t *testing.T) {
	ast, ds := parse(`wardley-beta
title Tea
size [1100, 800]
evolution Genesis@0.25 -> Custom / Concept -> Product@0.75
anchor Business [0.95, 0.63]
component Cup of Tea [0.79, 0.61] label [-60, 35] (build) (inertia)
component "Web App" [0.7, 0.8] (inertia)
Business -> Cup of Tea
"Web App" +<> Cup of Tea; note
Cup of Tea +'a b'> Business
evolve Cup of Tea 0.9
pipeline Cup of Tea {
  component Fire [0.3] label [1, -2]
  component Gas [0.5]
}
note "n" [0.1, 0.2]
annotations [0.1, 2]
annotation 3,[0.5, 7] "text"
accelerator A [0.1, 0.2]
deaccelerator D [0.3, 0.4]
`)
	require.Empty(t, messages(ds))
	require.Equal(t, "KW_WARDLEY", ast.Header.Kind)
	require.Equal(t, []Metadata{{Field: "title", Value: "Tea", Span: source.Span{Start: 13, End: 22}}}, ast.Metadata)
	require.Equal(t, "1100", ast.Size.Width.Text)
	require.Len(t, ast.Evolution.Stages, 3)
	require.Equal(t, "0.25", ast.Evolution.Stages[0].Boundary.Text)
	require.Equal(t, "Concept", ast.Evolution.Stages[1].SecondName.Text)
	require.Len(t, ast.Anchors, 1)
	require.Len(t, ast.Components, 2)
	cup := ast.Components[0]
	require.Equal(t, "Cup of Tea", cup.Name.Text)
	require.True(t, cup.Label.NegX)
	require.Equal(t, "60", cup.Label.OffsetX.Text)
	require.False(t, cup.Label.NegY)
	require.Equal(t, "build", cup.Decorator.Strategy.Text)
	require.True(t, cup.Inertia)
	require.True(t, ast.Components[1].Inertia)
	require.Nil(t, ast.Components[1].Decorator)
	require.Len(t, ast.Links, 3)
	require.Equal(t, "+<>", ast.Links[1].FromPort.Text)
	require.Equal(t, "note", ast.Links[1].LinkLabel.Text)
	require.Equal(t, "+'a b'>", ast.Links[2].Arrow.Text)
	require.Len(t, ast.Evolves, 1)
	require.Len(t, ast.Pipelines, 1)
	require.Len(t, ast.Pipelines[0].Components, 2)
	require.Equal(t, "2", ast.Pipelines[0].Components[0].Label.OffsetY.Text)
	require.True(t, ast.Pipelines[0].Components[0].Label.NegY)
	require.Len(t, ast.Notes, 1)
	require.Len(t, ast.Annotations, 1)
	require.Len(t, ast.Annotation, 1)
	require.Len(t, ast.Accelerators, 1)
	require.Len(t, ast.Deaccelerators, 1)
}

func TestSpansCoverStatementWithoutLineEnd(t *testing.T) {
	src := "wardley-beta\nanchor A [0.5, 0.5]\n\n\ncomponent B [0.1, 0.2]\n"
	ast, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, "anchor A [0.5, 0.5]", src[ast.Anchors[0].Span.Start:ast.Anchors[0].Span.End])
	require.Equal(t, "component B [0.1, 0.2]", src[ast.Components[0].Span.Start:ast.Components[0].Span.End])
	require.Equal(t, "A", src[ast.Anchors[0].Name.Span.Start:ast.Anchors[0].Name.Span.End])
}

func TestHyphenAndArrowTokenisation(t *testing.T) {
	ast, ds := parse("wardley-beta\nA->B\nfoo-bar->baz\nreal-time processing -> end-user\nfoo--bar -> x\nfoo- -> y\n")
	require.Empty(t, messages(ds))
	require.Len(t, ast.Links, 5)
	require.Equal(t, "A", ast.Links[0].From.Text)
	require.Equal(t, "B", ast.Links[0].To.Text)
	require.Equal(t, "foo-bar", ast.Links[1].From.Text)
	require.Equal(t, "baz", ast.Links[1].To.Text)
	require.Equal(t, "real-time processing", ast.Links[2].From.Text)
	require.Equal(t, "foo--bar", ast.Links[3].From.Text)
	require.Equal(t, "foo-", ast.Links[4].From.Text)
}

func TestTokenPriorityFollowsAuthority(t *testing.T) {
	require.Equal(t, []string{"KW_WARDLEY", "STRATEGY", "NAME_WITH_SPACES", "EOF"}, kinds("wardley-beta buyer"))
	require.Equal(t, []string{"KW_COMPONENT", "NAME_WITH_SPACES", "EOF"}, kinds("component Foo"))
	require.Equal(t, []string{"KW_COMPONENT", "ID", "EOF"}, kinds("component _foo"))
	require.Equal(t, []string{"STRING", "EOF"}, kinds(`"label"`))
	require.Equal(t, []string{"KW_SIZE", "NAME_WITH_SPACES", "EOF"}, kinds("sizes"))
	require.Equal(t, []string{"KW_WARDLEY", "NEWLINE", "NAME_WITH_SPACES", "EOF"}, kinds("wardley-beta\ntitleX"))
	require.Equal(t, []string{"KW_WARDLEY", "NEWLINE", "NAME_WITH_SPACES", "EOF"}, kinds("wardley-beta\ntitle"))
	require.Equal(t, []string{"KW_WARDLEY", "NEWLINE", "TITLE", "NEWLINE", "EOF"}, kinds("wardley-beta\ntitle\n"))
	require.Equal(t, []string{"KW_WARDLEY", "NEWLINE", "ID", "EOF"}, kinds("wardley-beta\naccTitleX"))
	require.Equal(t, []string{"INT", "ID", "INVALID", "EOF"}, kinds("12."))
	require.Equal(t, []string{"INT", "NAME_WITH_SPACES", "EOF"}, kinds("0abc"))
}

func TestHeaderFoldsCaseOnlyAtDocumentStart(t *testing.T) {
	ast, ds := parse("Wardley-Beta\ncomponent A [0.1, 0.1]\n")
	require.Empty(t, messages(ds))
	require.Equal(t, "Wardley-Beta", ast.Header.Text)
	require.Equal(t, []string{"KW_WARDLEY", "NEWLINE", "NAME_WITH_SPACES", "EOF"}, kinds("wardley-beta\nWardley-Beta"))
	_, ds = parse("wardley-beta\nWardley-Beta\n")
	require.NotEmpty(t, ds)
}

func TestKeywordsAreCaseSensitive(t *testing.T) {
	_, ds := parse("wardley-beta\nComponent A [0.1, 0.1]\n")
	require.Equal(t, []string{"wardley/unexpected-token: unexpected [, expected one of: ARROW, ID, LINK_ARROW, LINK_PORT, NAME_WITH_SPACES, STRING"}, messages(ds))
}

func TestDecimalCoordinatesRejectIntegers(t *testing.T) {
	_, ds := parse("wardley-beta\ncomponent A [1, 0.5]\n")
	require.Equal(t, []string{"wardley/unexpected-token: unexpected 1, expected one of: WARDLEY_NUMBER"}, messages(ds))
	_, ds = parse("wardley-beta\nannotations [1, 2]\nannotation 1,[1, 0.5] \"a\"\n")
	require.Empty(t, messages(ds))
}

func TestUnknownStatementSpansLine(t *testing.T) {
	src := "wardley-beta\n[x] y z\ncomponent A [0.1, 0.1]\n"
	ast, ds := parse(src)
	require.Equal(t, []string{"wardley/unknown-statement: unknown statement ["}, messages(ds))
	require.Equal(t, "[x] y z", src[ds[0].Span.Start:ds[0].Span.End])
	require.Len(t, ast.Components, 1)
}

func TestUnterminatedDelimiters(t *testing.T) {
	for _, tc := range []struct{ src, message string }{
		{"wardley-beta\ncomponent A [0.1, ", "wardley/unterminated: unterminated ["},
		{"wardley-beta\ncomponent A [0.1, 0.2] (", "wardley/unterminated: unterminated ("},
		{"wardley-beta\ncomponent A [0.1, 0.2] label [", "wardley/unterminated: unterminated ["},
		{"wardley-beta\npipeline P {\n", "wardley/unterminated: unterminated {"},
		{"wardley-beta\npipeline P {\ncomponent A [0.1", "wardley/unterminated: unterminated ["},
		{"wardley-beta\nnote \"never closed", "wardley/unterminated: unterminated \""},
		{"wardley-beta\naccDescr {\nnever closed", "wardley/unterminated: unterminated {"},
	} {
		_, ds := parse(tc.src)
		require.Equal(t, []string{tc.message}, messages(ds), tc.src)
		require.Equal(t, len(tc.src), ds[0].Span.End, tc.src)
	}
}

func TestPipelineRecovery(t *testing.T) {
	src := "wardley-beta\npipeline P {\n  note x\n  component A [0.1]\n  component B [x]\n  component C [0.3] }\ncomponent D [0.1, 0.2]\n"
	ast, ds := parse(src)
	require.Len(t, ds, 3)
	require.Equal(t, "wardley/unexpected-token", ds[0].Code)
	require.Len(t, ast.Pipelines, 1)
	require.Len(t, ast.Pipelines[0].Components, 1)
	require.Len(t, ast.Components, 1)
}

func TestPipelineNeedsComponentsAndNewline(t *testing.T) {
	_, ds := parse("wardley-beta\npipeline P {\n}\n")
	require.Equal(t, []string{"wardley/unexpected-token: unexpected }, expected one of: KW_COMPONENT"}, messages(ds))
	_, ds = parse("wardley-beta\npipeline P { component A [0.1]\n}\n")
	require.Equal(t, []string{"wardley/unexpected-token: unexpected component, expected one of: NEWLINE", "wardley/unknown-statement: unknown statement }"}, messages(ds))
}

func TestMetadata(t *testing.T) {
	ast, ds := parse("wardley-beta\ntitle  A   B  %% c\naccTitle: t\naccDescr: d\naccDescr {\n  x\n\n  y\n}\n")
	require.Empty(t, messages(ds))
	var values []string
	for _, m := range ast.Metadata {
		values = append(values, m.Field+"="+m.Value)
	}
	require.Equal(t, []string{"title=A B", "accTitle=t", "accDescr=d", "accDescr=x\ny"}, values)
}

func TestStringEscapes(t *testing.T) {
	ast, ds := parse("wardley-beta\nnote \"a\\\"b\\n\" [0.1, 0.2]\ncomponent 'x\\'y' [0.1, 0.2]\n")
	require.Empty(t, messages(ds))
	require.Equal(t, "a\"b\n", ast.Notes[0].Text.Text)
	require.Equal(t, "x'y", ast.Components[0].Name.Text)
}

func TestEvolutionNeedsTwoStages(t *testing.T) {
	_, ds := parse("wardley-beta\nevolution A\n")
	require.Equal(t, []string{"wardley/unexpected-token: unexpected \n, expected one of: /, @, ARROW"}, messages(ds))
}

func TestLinkPortsAndArrows(t *testing.T) {
	ast, ds := parse("wardley-beta\nA +> B\nA -.-> B\nA --> B +<\nA > B\n")
	require.Empty(t, messages(ds))
	require.Len(t, ast.Links, 4)
	require.Equal(t, "+>", ast.Links[0].FromPort.Text)
	require.Equal(t, "-.->", ast.Links[1].Arrow.Text)
	require.Equal(t, "+<", ast.Links[2].ToPort.Text)
	require.Equal(t, ">", ast.Links[3].Arrow.Text)
}

func TestInvalidByteIsRejected(t *testing.T) {
	_, ds := parse("wardley-beta\ncomponent A [0.1, 0.1] .\n")
	require.Equal(t, []string{"wardley/unexpected-token: unexpected ., expected one of: (, EOF, KW_INERTIA, KW_LABEL, NEWLINE"}, messages(ds))
}
