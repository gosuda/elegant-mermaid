package journey_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/journey"
)

func parse(src string) (*parser.Start, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	return parser.Parse([]byte(src), prep.Removed)
}

func statements(start *parser.Start) []parser.StatementKind {
	var out []parser.StatementKind
	for _, line := range start.Document.Lines {
		if line.Statement != nil {
			out = append(out, line.Statement.Kind)
		}
	}
	return out
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func slice(src string, span source.Span) string { return src[span.Start:span.End] }

func TestStatementForms(t *testing.T) {
	src := "journey\ntitle  My day\naccTitle: A title \naccDescr: A line\nsection Go\n  Make tea: 5: Me\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 5)
	title := kinds[0].(*parser.Title)
	require.Equal(t, " My day", title.Text.Text)
	require.Equal(t, " My day", slice(src, title.Text.Span))
	require.Equal(t, "A title ", kinds[1].(*parser.AccTitle).Value.Text)
	require.Equal(t, "A line", kinds[2].(*parser.AccDescr).Value.Text)
	require.Equal(t, "Go", kinds[3].(*parser.Section).Text.Text)
	task := kinds[4].(*parser.Task)
	require.Equal(t, "Make tea", task.Name.Text)
	require.Equal(t, ": 5: Me", task.Data.Text)
	require.Equal(t, "journey", slice(src, start.Header.Span))
	require.Equal(t, 0, start.Span.Start)
	require.Equal(t, "title  My day", slice(src, start.Document.Lines[1].Span))
}

func TestTaskFieldsKeepSpans(t *testing.T) {
	src := "journey\n  Do work :  1 : Me, Cat :extra\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	task := statements(start)[0].(*parser.Task)
	require.Equal(t, "Do work ", task.Name.Text)
	require.Len(t, task.Fields, 3)
	raw := []string{"  1 ", " Me, Cat ", "extra"}
	trimmed := []string{"1", "Me, Cat", "extra"}
	for i, field := range task.Fields {
		require.Equal(t, raw[i], field.Raw.Text)
		require.Equal(t, raw[i], slice(src, field.Raw.Span))
		require.Equal(t, trimmed[i], field.Trimmed.Text)
		require.Equal(t, trimmed[i], slice(src, field.Trimmed.Span))
	}
}

func TestEmptyTrailingFieldsStayAsFields(t *testing.T) {
	start, ds := parse("journey\nT: 3:\nU: :\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds[0].(*parser.Task).Fields, 2)
	second := kinds[1].(*parser.Task).Fields
	require.Len(t, second, 2)
	require.Equal(t, second[0].Raw.Span.Start, second[0].Trimmed.Span.Start)
	require.Equal(t, second[0].Trimmed.Span.Start, second[0].Trimmed.Span.End)
}

func TestKeywordsMatchWithoutRegardToCaseAndTakeAnyLeadingWhitespaceChar(t *testing.T) {
	start, ds := parse("JOURNEY\nTITLE x\nSection\ty\nACCTITLE:z\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Equal(t, "x", kinds[0].(*parser.Title).Text.Text)
	require.Equal(t, "y", kinds[1].(*parser.Section).Text.Text)
	require.Equal(t, "z", kinds[2].(*parser.AccTitle).Value.Text)
}

func TestTitleKeywordOutranksTaskName(t *testing.T) {
	start, ds := parse("journey\nTitle page: 3: Me\n")
	require.Empty(t, ds)
	require.Equal(t, "page: 3: Me", statements(start)[0].(*parser.Title).Text.Text)
}

func TestSemicolonIsInvalidAndRecoveryStopsAtLineEnd(t *testing.T) {
	src := "journey\nA: 3; B: 4\nC: 2\n"
	start, ds := parse(src)
	require.Equal(t, []string{"journey/unknown-statement: unknown statement ;"}, messages(ds))
	require.Equal(t, "; B: 4", slice(src, ds[0].Span))
	kinds := statements(start)
	require.Len(t, kinds, 2)
	require.Equal(t, "C", kinds[1].(*parser.Task).Name.Text)
}

func TestTaskWithoutDataIsRejectedOnce(t *testing.T) {
	src := "journey\nLonely\nB: 4\n"
	start, ds := parse(src)
	require.Equal(t, []string{"journey/unexpected-token: unexpected end of line, expected one of: taskData"}, messages(ds))
	require.Equal(t, "\n", slice(src, ds[0].Span))
	require.Len(t, statements(start), 1)
}

func TestBareColonAfterNameIsRejected(t *testing.T) {
	src := "journey\nName :\nB: 4\n"
	start, ds := parse(src)
	require.Equal(t, []string{"journey/unexpected-token: unexpected :, expected one of: taskData"}, messages(ds))
	require.Equal(t, ":", slice(src, ds[0].Span))
	require.Len(t, statements(start), 1)
}

func TestStandaloneDataAndHeaderRepeatAreUnknownStatements(t *testing.T) {
	src := "journey\n: 4: x\njourney\nB: 4\n"
	start, ds := parse(src)
	require.Equal(t, []string{"journey/unknown-statement: unknown statement : 4: x", "journey/unknown-statement: unknown statement journey"}, messages(ds))
	require.Len(t, statements(start), 1)
}

func TestHeaderWordNeedsBoundary(t *testing.T) {
	start, ds := parse("journey\njourneys: 3\n")
	require.Empty(t, ds)
	require.Equal(t, "journeys", statements(start)[0].(*parser.Task).Name.Text)
}

func TestMultilineDescriptionKeepsBracesAndTrimsNothing(t *testing.T) {
	src := "journey\naccDescr {\n  first\n  second\n}\nA: 3\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	block := statements(start)[0].(*parser.AccDescrMultiline)
	require.Equal(t, "first\n  second\n", block.Value.Text)
	require.Equal(t, "{", slice(src, block.Open))
	require.NotNil(t, block.Close)
	require.Equal(t, "}", slice(src, *block.Close))
	require.Len(t, statements(start), 2)
}

func TestEmptyMultilineDescriptionMakesNoStatement(t *testing.T) {
	start, ds := parse("journey\naccDescr {\n}\n")
	require.Empty(t, ds)
	require.Empty(t, statements(start))
}

func TestUnterminatedDescriptionSpansToEOF(t *testing.T) {
	src := "journey\naccDescr {\nnever closed"
	start, ds := parse(src)
	require.Equal(t, []string{"journey/unterminated: unterminated {"}, messages(ds))
	require.Equal(t, "{\nnever closed", slice(src, ds[0].Span))
	block := statements(start)[0].(*parser.AccDescrMultiline)
	require.Nil(t, block.Close)
	require.Equal(t, "never closed", block.Value.Text)
}

func TestQuotesNeverUnterminate(t *testing.T) {
	_, ds := parse("journey\nSay \"hi: 3\nB: 4\n")
	require.Empty(t, ds)
}

func TestAccessibilityValuesKeepHashAndSemicolon(t *testing.T) {
	start, ds := parse("journey\naccTitle: a # b; c\naccDescr: d # e; f\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Equal(t, "a # b; c", kinds[0].(*parser.AccTitle).Value.Text)
	require.Equal(t, "d # e; f", kinds[1].(*parser.AccDescr).Value.Text)
}

func TestAccessibilityColonConsumesLineBreakWhitespace(t *testing.T) {
	start, ds := parse("journey\naccTitle:\n  value\n")
	require.Empty(t, ds)
	require.Equal(t, "value", statements(start)[0].(*parser.AccTitle).Value.Text)
}

func TestEmptyAccessibilityValueAtEOF(t *testing.T) {
	start, ds := parse("journey\naccTitle:")
	require.Empty(t, ds)
	require.Equal(t, "", statements(start)[0].(*parser.AccTitle).Value.Text)
}

func TestCommentsAreSkipped(t *testing.T) {
	src := "journey\n%% whole line\n# hash line\nA: 3 # tail\nB: 4: Me %% inline\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 2)
	require.Equal(t, ": 3 ", kinds[0].(*parser.Task).Data.Text)
	require.Equal(t, ": 4: Me %% inline", kinds[1].(*parser.Task).Data.Text)
}

func TestCommentAfterOneCharacterIsDiscardedWithThatCharacter(t *testing.T) {
	start, ds := parse("journey\n  x%%rest\nB: 4\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 1)
	require.Equal(t, "B", kinds[0].(*parser.Task).Name.Text)
}

func TestCRLFSpansPointAtSourceBytes(t *testing.T) {
	src := "journey\r\nA: 3: Me\r\nB: 4\r\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	kinds := statements(start)
	require.Equal(t, "Me", slice(src, kinds[0].(*parser.Task).Fields[1].Trimmed.Span))
	require.Equal(t, "B: 4", slice(src, start.Document.Lines[len(start.Document.Lines)-2].Span))
}

func TestDirectiveInsideTaskKeepsSpansOnSourceBytes(t *testing.T) {
	src := "journey\nA: 3: M%%{init: {}}%%e\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	field := statements(start)[0].(*parser.Task).Fields[1]
	require.Equal(t, "Me", field.Trimmed.Text)
	require.Equal(t, "M%%{init: {}}%%e", slice(src, field.Trimmed.Span))
}

func TestEmptyDocumentAfterHeader(t *testing.T) {
	start, ds := parse("journey")
	require.Empty(t, ds)
	require.Empty(t, start.Document.Lines)
	require.Equal(t, source.Span{Start: 7, End: 7}, start.Document.Span)
}

func TestFirstWordMustBeHeader(t *testing.T) {
	_, ds := parse("pie\nA: 3")
	require.Equal(t, []string{"journey/unexpected-token: unexpected pie, expected one of: journey"}, messages(ds))
}

func TestEntitiesAreTextAndDoNotStartComments(t *testing.T) {
	src := "journey\nsection R#38;D #amp; Q\nA #35; b: 3: x#60;y\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	kinds := statements(start)
	require.Equal(t, "R#38;D #amp; Q", kinds[0].(*parser.Section).Text.Text)
	task := kinds[1].(*parser.Task)
	require.Equal(t, "A #35; b", task.Name.Text)
	require.Equal(t, "x#60;y", task.Fields[1].Trimmed.Text)
}

func TestMalformedEntityStillStartsAComment(t *testing.T) {
	start, ds := parse("journey\nA: 3 #amp\nB: 4 #;\nC: 5 ##amp; x\n")
	require.Empty(t, ds)
	kinds := statements(start)
	require.Len(t, kinds, 3)
	require.Equal(t, ": 3 ", kinds[0].(*parser.Task).Data.Text)
	require.Equal(t, ": 4 ", kinds[1].(*parser.Task).Data.Text)
	require.Equal(t, ": 5 ", kinds[2].(*parser.Task).Data.Text)
}
