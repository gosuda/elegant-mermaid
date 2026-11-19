package journey_test

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/journey"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/journey"
)

func resolve(src string) (*model.Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	start, parsed := parser.Parse([]byte(src), prep.Removed)
	m, resolved := model.Resolve([]byte(src), start)
	return m, append(parsed, resolved...)
}

func messages(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func TestSectionsTasksAndActors(t *testing.T) {
	src := "journey\ntitle  My day\nsection Go\n  Make tea: 5: Me\n  Do work: 1: Me, Cat\nsection Home\n  Sit: 5\n"
	m, ds := resolve(src)
	require.Empty(t, ds)
	require.Equal(t, " My day", m.Title)
	require.Equal(t, "My day", m.TitleLabel)
	require.Len(t, m.Sections, 2)
	require.Len(t, m.Tasks, 3)
	require.Equal(t, "Go", m.Tasks[0].Section)
	require.Equal(t, "Home", m.Tasks[2].Section)
	require.Equal(t, 5, m.Tasks[0].Score)
	require.Equal(t, []string{"Me", "Cat"}, m.Tasks[1].People)
	require.Nil(t, m.Tasks[2].People)
	require.Equal(t, []string{"Cat", "Me"}, m.Actors)
	require.Equal(t, "Make tea", m.Tasks[0].Name)
	require.Equal(t, "Sit", m.Tasks[2].Label)
}

func TestTasksBeforeAnySectionStayInTheEmptySection(t *testing.T) {
	m, ds := resolve("journey\nA: 3\nsection S\nB: 4\n")
	require.Empty(t, ds)
	require.Equal(t, "", m.Tasks[0].Section)
	require.Equal(t, "S", m.Tasks[1].Section)
}

func TestDuplicateSectionsRemainDuplicate(t *testing.T) {
	m, ds := resolve("journey\nsection S\nsection S\nA: 3\n")
	require.Empty(t, ds)
	require.Len(t, m.Sections, 2)
}

func TestSectionAndTaskNamesAreNotTrimmedButLabelsAre(t *testing.T) {
	m, ds := resolve("journey\nsection  Wide \n  register slug : 5: x\n")
	require.Empty(t, ds)
	require.Equal(t, " Wide ", m.Sections[0].Name)
	require.Equal(t, "Wide", m.Sections[0].Label)
	require.Equal(t, "register slug ", m.Tasks[0].Name)
	require.Equal(t, "register slug", m.Tasks[0].Label)
}

func TestPeopleKeepOrderDuplicatesAndEmptyNames(t *testing.T) {
	m, ds := resolve("journey\nA: 3: Bob, ,bob,Bob :ignored\nB: 3:\nC: 3\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"Bob", "", "bob", "Bob"}, m.Tasks[0].People)
	require.Equal(t, []string{""}, m.Tasks[1].People)
	require.Nil(t, m.Tasks[2].People)
	require.Equal(t, []string{"", "Bob", "bob"}, m.Actors)
}

func TestActorsSortByUTF16CodeUnits(t *testing.T) {
	m, ds := resolve("journey\nA: 3: \uffee, \U0001F600, z\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"z", "\U0001F600", "\uffee"}, m.Actors)
}

func TestScoreMustBeAnIntegerInRange(t *testing.T) {
	cases := map[string]string{
		"abc":                      "journey/unexpected-token: unexpected abc, expected one of: integer",
		"":                         "journey/unexpected-token: unexpected , expected one of: integer",
		"3.5":                      "journey/unexpected-token: unexpected 3.5, expected one of: integer",
		"1e2":                      "journey/unexpected-token: unexpected 1e2, expected one of: integer",
		"+-3":                      "journey/unexpected-token: unexpected +-3, expected one of: integer",
		"0":                        "journey/score-out-of-range: score 0 is outside the range 1 to 5",
		"6":                        "journey/score-out-of-range: score 6 is outside the range 1 to 5",
		"-1":                       "journey/score-out-of-range: score -1 is outside the range 1 to 5",
		"007":                      "journey/score-out-of-range: score 007 is outside the range 1 to 5",
		"99999999999999999999999":  "journey/score-out-of-range: score 99999999999999999999999 is outside the range 1 to 5",
		"-99999999999999999999999": "journey/score-out-of-range: score -99999999999999999999999 is outside the range 1 to 5",
	}
	for field, want := range cases {
		_, ds := resolve("journey\nA: " + field + "\n")
		require.Equal(t, []string{want}, messages(ds), "field %q", field)
	}
}

func TestScoreAcceptsSignsAndLeadingZeros(t *testing.T) {
	m, ds := resolve("journey\nA: +5\nB: 003\nC:  4 \n")
	require.Empty(t, ds)
	require.Equal(t, []int{5, 3, 4}, []int{m.Tasks[0].Score, m.Tasks[1].Score, m.Tasks[2].Score})
}

func TestScoreDiagnosticSpansCoverTheTrimmedField(t *testing.T) {
	src := "journey\nA:  9 : Me\nB: \n"
	_, ds := resolve(src)
	require.Len(t, ds, 2)
	require.Equal(t, "9", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, ds[1].Span.Start, ds[1].Span.End)
}

func TestAccessibilityAndTitleReplacePreviousValues(t *testing.T) {
	src := "journey\ntitle one\ntitle two\naccTitle:  first \naccTitle: second\naccDescr: d1\naccDescr {\n  line one\n    line two\n}\n"
	m, ds := resolve(src)
	require.Empty(t, ds)
	require.Equal(t, "two", m.Title)
	require.Equal(t, "second", m.AccTitle)
	require.Equal(t, "line one\nline two", m.AccDescr)
}

func TestLabelsDecodeEntities(t *testing.T) {
	m, ds := resolve("journey\nsection R#38;D #amp; Q\nA #35; b: 3\n")
	require.Empty(t, ds)
	require.Equal(t, "R&D & Q", m.Sections[0].Label)
	require.Equal(t, "A # b", m.Tasks[0].Label)
}

func TestHonouredConfigKeys(t *testing.T) {
	m, ds := resolve("%%{init: {\"journey\": {\"width\": 200, \"height\": 60, \"diagramMarginX\": 10, \"ignored\": 3}}}%%\njourney\nA: 3\n")
	require.Empty(t, ds)
	require.Equal(t, model.Config{Width: 200, WidthSet: true, Height: 60, HeightSet: true, MarginX: 10, MarginXSet: true}, m.Config)
}

func TestUnparsedStatementsCreateNoTasks(t *testing.T) {
	m, ds := resolve("journey\nLonely\n; x\nA: 3\n")
	require.Len(t, ds, 2)
	require.Len(t, m.Tasks, 1)
}
