package eventmodeling_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/eventmodeling"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/eventmodeling"
)

func parse(src string) (*parser.EventModel, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	return parser.Parse([]byte(src), prep.Removed)
}

func accepted(src string) bool {
	document, ds := parse(src)
	_, resolved := model.Resolve(document)
	for _, d := range append(ds, resolved...) {
		if d.Severity == diag.SeverityError {
			return false
		}
	}
	return true
}

type verdictCase struct {
	Name   string `json:"name"`
	Source string `json:"source"`
	Accept bool   `json:"accept"`
}

func TestVerdictsMatchUpstream(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "..", "..", "spec", "golden", "eventmodeling", "syntax-cases.json"))
	require.NoError(t, err)
	var cases []verdictCase
	require.NoError(t, json.Unmarshal(data, &cases))
	require.NotEmpty(t, cases)
	for _, c := range cases {
		require.Equal(t, c.Accept, accepted(c.Source), "%s: %q", c.Name, c.Source)
	}
}

func TestCorpusAccepted(t *testing.T) {
	paths, err := filepath.Glob(filepath.Join("..", "..", "..", "corpus", "eventmodeling", "*", "*.mmd"))
	require.NoError(t, err)
	require.NotEmpty(t, paths)
	for _, path := range paths {
		src, err := os.ReadFile(path)
		require.NoError(t, err)
		require.True(t, accepted(string(src)), path)
	}
}

func rendered(src string, ds []diag.Diagnostic) []string {
	var out []string
	for _, d := range ds {
		out = append(out, d.Code+" | "+d.Message+" | "+src[d.Span.Start:d.Span.End])
	}
	return out
}

func TestDiagnostics(t *testing.T) {
	cases := []struct {
		src  string
		want []string
	}{
		{"eventmodeling\ntitle My Title\ntf 01 ui A\n", []string{"eventmodeling/unknown-statement | unknown statement title | title My Title"}},
		{"eventmodeling\ntf 01 ui A; tf 02 cmd B\n", []string{"eventmodeling/unknown-statement | unknown statement ; | ; "}},
		{"eventmodeling\ntf 01 ui\ntf 02 cmd B\n", []string{"eventmodeling/unexpected-token | unexpected tf, expected one of: EM_ID | tf"}},
		{"eventmodeling\ntf 01 ui A ->>\ntf 02 cmd B\n", []string{"eventmodeling/unexpected-token | unexpected tf, expected one of: EM_FID | tf"}},
		{"eventmodeling\ntf 01 foo A\n", []string{"eventmodeling/unexpected-token | unexpected foo, expected one of: cmd, command, event, evt, pcr, processor, readmodel, rmo, ui | foo"}},
		{"eventmodeling\ntf 01 ui A [[N", []string{"eventmodeling/unterminated | unterminated [[ | [[N"}},
		{"eventmodeling\ntf 01 ui A [[N tf 02 ui B", []string{"eventmodeling/unexpected-token | unexpected tf, expected one of: ]] | tf"}},
		{"eventmodeling\ntf 01 ui A `json", []string{"eventmodeling/unterminated | unterminated ` | `json"}},
		{"eventmodeling\ntf 01 ui A `foo` { a }\n", []string{"eventmodeling/unexpected-token | unexpected foo, expected one of: figma, html, jsobj, json, md, salt, text, uri | foo"}},
		{"eventmodeling\ntf 01 ui A \"x\ntf 02 ui B\n", []string{"eventmodeling/unterminated | unterminated \" | \"x\ntf 02 ui B\n"}},
		{"eventmodeling\n/* open\ntf 01 ui A\n", []string{"eventmodeling/unterminated | unterminated /* | /* open\ntf 01 ui A\n"}},
		{"eventmodeling\ndata D { a }\n", []string{"eventmodeling/unexpected-token | unexpected { a }, expected one of: EM_DATA_BLOCK, ` | { a }"}},
		{"eventmodeling\ngwt 01 given ui A then evt B tf 02 ui C\n", nil},
		{"eventmodeling\ngwt 01 then evt B\n", []string{"eventmodeling/unexpected-token | unexpected then, expected one of: given | then"}},
		{"eventmodeling\nfoo bar baz\ntf 01 ui A\n", []string{"eventmodeling/unknown-statement | unknown statement foo | foo bar baz"}},
		{"eventmodeling foo\ntf 01 ui A\n", []string{"eventmodeling/unknown-statement | unknown statement foo | foo"}},
		{"eventmodeling;\ntf 01 ui A\n", []string{"eventmodeling/unexpected-token | unexpected eventmodeling, expected one of: eventmodeling | eventmodeling"}},
		{"eventmodeling\ntf 01 ui A\n  ui B\n", []string{"eventmodeling/unknown-statement | unknown statement ui | ui B"}},
		{"eventmodeling\ntf 1000 ui A\n", []string{"eventmodeling/unexpected-token | unexpected 0, expected one of: cmd, command, event, evt, pcr, processor, readmodel, rmo, ui | 0"}},
	}
	for _, c := range cases {
		_, ds := parse(c.src)
		require.Equal(t, c.want, rendered(c.src, ds), "%q", c.src)
	}
}

func TestEndOfInputInsideDelimiterReportsOnlyUnterminated(t *testing.T) {
	for _, src := range []string{"eventmodeling\ntf 01 ui A [[", "eventmodeling\ntf 01 ui A [[N", "eventmodeling\ntf 01 ui A `", "eventmodeling\ntf 01 ui A `json", "eventmodeling\ntf 01 ui A `json`"[:len("eventmodeling\ntf 01 ui A `json")]} {
		_, ds := parse(src)
		require.Len(t, ds, 1, src)
		require.Equal(t, "eventmodeling/unterminated", ds[0].Code, src)
		require.Equal(t, len(src), ds[0].Span.End, src)
	}
}

func TestEndOfInputShowsZeroWidthSpan(t *testing.T) {
	src := "eventmodeling\ntf 01 ui A ->>"
	_, ds := parse(src)
	require.Len(t, ds, 1)
	require.Equal(t, "eventmodeling/unexpected-token", ds[0].Code)
	require.Equal(t, len(src), ds[0].Span.Start)
	require.Equal(t, len(src), ds[0].Span.End)
}

func TestRecoveryKeepsLaterStatements(t *testing.T) {
	src := "eventmodeling\ntf 01 ui A\nbogus line here\ntf 02 cmd B ->>\ntf 03 evt C\nentity X\ntf 04 ui D; tf 05 ui E\n"
	document, ds := parse(src)
	require.Len(t, ds, 3)
	names := make([]string, len(document.Frames))
	for i, frame := range document.Frames {
		names[i] = frame.Fields().Name.Text
	}
	require.Equal(t, []string{"01", "03", "04", "05"}, names)
	require.Len(t, document.ModelEntities, 1)
}

func TestFramesAreFreeForm(t *testing.T) {
	src := "eventmodeling tf 01 ui A tf 02\ncmd B\n->> 01 { x } rf 03 evt C"
	document, ds := parse(src)
	require.Empty(t, ds)
	require.Len(t, document.Frames, 3)
	second := document.Frames[1].Fields()
	require.Equal(t, "02", second.Name.Text)
	require.Equal(t, []string{"01"}, []string{second.SourceFrames[0].Text})
	require.Equal(t, "{ x }", second.DataInlineValue.Text)
	_, reset := document.Frames[2].(*parser.EmResetFrame)
	require.True(t, reset)
}

func TestFrameSpansAndFields(t *testing.T) {
	src := "eventmodeling\ntf 02 cmd Inv . Add ->> 01 ->> 07 [[Info]] `json` {a}   // note\ntimeframe 03 evt X"
	document, ds := parse(src)
	require.Empty(t, ds)
	first := document.Frames[0].Fields()
	require.Equal(t, "tf 02 cmd Inv . Add ->> 01 ->> 07 [[Info]] `json` {a}", src[first.Span.Start:first.Span.End])
	require.Equal(t, "tf", src[first.Keyword.Start:first.Keyword.End])
	require.Equal(t, "Inv.Add", first.EntityIdentifier.Text)
	require.Equal(t, "Inv . Add", src[first.EntityIdentifier.Span.Start:first.EntityIdentifier.Span.End])
	require.Equal(t, "cmd", first.ModelEntityType.Text)
	require.Equal(t, "Info", first.DataReference.Text)
	require.Equal(t, "Info", src[first.DataReference.Span.Start:first.DataReference.Span.End])
	require.Equal(t, "json", first.DataType.Text)
	require.Equal(t, "{a}", src[first.DataInlineValue.Span.Start:first.DataInlineValue.Span.End])
	require.Len(t, first.SourceFrames, 2)
	last := document.Frames[1].Fields()
	require.Equal(t, "timeframe 03 evt X", src[last.Span.Start:last.Span.End])
	require.Nil(t, last.DataType)
	require.Nil(t, last.DataReference)
	require.Nil(t, last.DataInlineValue)
}

func TestStatementLists(t *testing.T) {
	src := "eventmodeling\nentity A.B\ndata D `json` {\n x\n}\nnote 01 {\n y\n}\ngwt 01 given ui A cmd B when evt C then rmo D pcr E\ntf 01 ui A\n"
	document, ds := parse(src)
	require.Empty(t, ds)
	require.Len(t, document.ModelEntities, 1)
	require.Equal(t, "A.B", document.ModelEntities[0].Name.Text)
	require.Len(t, document.DataEntities, 1)
	data := document.DataEntities[0]
	require.Equal(t, "D", data.Name.Text)
	require.Equal(t, "json", data.DataType.Text)
	require.Equal(t, "{\n x\n}\n", data.DataBlockValue.Text)
	require.Len(t, document.NoteEntities, 1)
	require.Equal(t, "01", document.NoteEntities[0].SourceFrame.Text)
	require.Len(t, document.GwtEntities, 1)
	gwt := document.GwtEntities[0]
	require.Len(t, gwt.GivenStatements, 2)
	require.Len(t, gwt.WhenStatements, 1)
	require.Len(t, gwt.ThenStatements, 2)
	require.Equal(t, "pcr", gwt.ThenStatements[1].ModelEntityType.Text)
	require.Equal(t, "E", gwt.ThenStatements[1].EntityIdentifier.Text)
}

func TestMetadataStatementsAreNotRecognised(t *testing.T) {
	for _, src := range []string{"eventmodeling\ntitle T\n", "eventmodeling\naccTitle: T\n", "eventmodeling\naccDescr: T\n", "eventmodeling\naccDescr {\nT\n}\n"} {
		require.False(t, accepted(src), src)
	}
}

func TestKeywordsAreReservedIdentifiersKeepPrefixes(t *testing.T) {
	require.True(t, accepted("eventmodeling\ntf 01 ui datax\ntf 02 ui uiX\ntf 03 ui tfx\n"))
	for _, name := range []string{"data", "text", "tf", "ui", "given", "entity"} {
		require.False(t, accepted("eventmodeling\ntf 01 ui "+name+"\n"), name)
	}
}

func TestBlockDataBoundaries(t *testing.T) {
	require.True(t, accepted("eventmodeling\ndata D {\n a\n} \n"))
	require.True(t, accepted("eventmodeling\ndata D {\n a\n}"))
	require.False(t, accepted("eventmodeling\ndata D {\n a\n}x\n"))
	require.False(t, accepted("eventmodeling\ndata D {\n a\n }\n"))
	document, _ := parse("eventmodeling\ndata D {\n}\n}\n")
	require.Equal(t, "{\n}\n}\n", document.DataEntities[0].DataBlockValue.Text)
	document, _ = parse("eventmodeling\ndata D {\r\n a\r\n}\r\ntf 01 ui A")
	require.Equal(t, "{\r\n a\r\n}\r\n", document.DataEntities[0].DataBlockValue.Text)
	require.Len(t, document.Frames, 1)
}

func TestInlineDataIsGreedyToLastCloserOnTheLine(t *testing.T) {
	document, ds := parse("eventmodeling\ntf 01 evt A { a } tf 02 evt B { b }\ntf 03 evt C\n")
	require.Empty(t, ds)
	require.Len(t, document.Frames, 2)
	require.Equal(t, "{ a } tf 02 evt B { b }", document.Frames[0].Fields().DataInlineValue.Text)
}

func TestDirectivesAndFrontmatterAreRemoved(t *testing.T) {
	src := "---\ntitle: x\n---\n%%{init: {\"theme\": \"dark\"}}%%\neventmodeling\ntf 01 ui A %%{init: {}}%%\ntf 02 cmd B\n"
	document, ds := parse(src)
	require.Empty(t, ds)
	require.Len(t, document.Frames, 2)
	require.True(t, strings.HasPrefix(src[document.Header.Span.Start:], "eventmodeling"))
}
