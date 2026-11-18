package timeline

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/timeline"
)

func resolve(src string) (*Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	start, parsed := syn.Parse([]byte(src), prep.Removed)
	m, resolved := Resolve([]byte(src), start)
	return m, append(parsed, resolved...)
}

func outline(m *Model) []string {
	var out []string
	for _, p := range m.Periods {
		line := p.SectionName + "|" + p.Text
		for _, e := range p.Events {
			line += "|" + e.Text
		}
		out = append(out, line)
	}
	return out
}

func TestDirectionDefaultsToLR(t *testing.T) {
	for src, want := range map[string]string{"timeline": "LR", "timeline LR": "LR", "timeline TD": "TD", "timeline td": "TD"} {
		m, ds := resolve(src)
		require.Empty(t, ds, src)
		require.Equal(t, want, m.Direction, src)
		require.Equal(t, want == "TD", m.Vertical(), src)
	}
}

func TestPeriodsEventsAndSectionsFollowDeclarationOrder(t *testing.T) {
	m, ds := resolve("timeline\nsection A\n2002 : x : y\n  : z\n2003\nsection B\n2004 : w\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"A|2002 |x |y|z", "A|2003", "B|2004 |w"}, outline(m))
	require.Equal(t, []int{0, 0, 1}, []int{m.Periods[0].Section, m.Periods[1].Section, m.Periods[2].Section})
	require.Equal(t, "A", m.Sections[0].Name)
	require.Equal(t, "B", m.Sections[1].Name)
}

func TestSectionNamesAreNotTrimmedAndDuplicatesStayDistinct(t *testing.T) {
	m, ds := resolve("timeline\nsection  A \n1\nsection  A \n2\n")
	require.Empty(t, ds)
	require.Equal(t, []string{" A ", " A "}, []string{m.Sections[0].Name, m.Sections[1].Name})
	require.Equal(t, []string{"A", "A"}, []string{m.Sections[0].Label, m.Sections[1].Label})
	require.Equal(t, []int{0, 1}, []int{m.Periods[0].Section, m.Periods[1].Section})
}

func TestPeriodsBeforeTheFirstSectionHaveNoSection(t *testing.T) {
	m, ds := resolve("timeline\n1\nsection S\n2\n")
	require.Empty(t, ds)
	require.Equal(t, []int{NoSection, 0}, []int{m.Periods[0].Section, m.Periods[1].Section})
	require.Equal(t, "", m.Periods[0].SectionName)
}

func TestEventAfterASectionStillBelongsToThePrecedingPeriod(t *testing.T) {
	m, ds := resolve("timeline\np : a\nsection S\n: b\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"|p |a|b"}, outline(m))
	require.Equal(t, NoSection, m.Periods[0].Section)
}

func TestEventWithoutAPeriodIsReported(t *testing.T) {
	m, ds := resolve("timeline\nsection S\n: lonely\np\n")
	require.Len(t, ds, 1)
	require.Equal(t, "timeline/event-without-period", ds[0].Code)
	require.Equal(t, "event has no preceding period", ds[0].Message)
	require.Equal(t, source.Span{Start: 19, End: 27}, ds[0].Span)
	require.Equal(t, []string{"S|p"}, outline(m))
}

func TestTitleKeepsItsLeadingWhitespaceAndTheLabelTrims(t *testing.T) {
	m, ds := resolve("timeline\ntitle   Social media \ntitle  last wins\n")
	require.Empty(t, ds)
	require.Equal(t, " last wins", m.Title)
	require.Equal(t, "last wins", m.TitleLabel)
}

func TestAccessibilityTextFollowsTheCommonDatabase(t *testing.T) {
	m, ds := resolve("timeline\naccTitle:   spaced title  \naccDescr {\n   line one\n \n     line two  \n}\n")
	require.Empty(t, ds)
	require.Equal(t, "spaced title", m.AccTitle)
	require.Equal(t, "line one\nline two", m.AccDescr)
	m, _ = resolve("timeline\naccDescr: first\naccDescr {second}\naccDescr {  }\n")
	require.Equal(t, "second", m.AccDescr)
}

func TestLabelsDecodeEntitiesAndTrimWithoutChangingTheText(t *testing.T) {
	m, ds := resolve("timeline\nsection #35;s#amp;\n  2002 : a #35;#9731; b #foo; #0; #x\n")
	require.Empty(t, ds)
	require.Equal(t, "#s&", m.Sections[0].Label)
	require.Equal(t, "2002", m.Periods[0].Label)
	require.Equal(t, "a #\u2603 b #foo; #0; #x", m.Periods[0].Events[0].Label)
	require.Equal(t, "a #35;#9731; b #foo; #0; #x", m.Periods[0].Events[0].Text)
}

func TestResolveIsRepeatable(t *testing.T) {
	src := "timeline\nsection S\np : e\n"
	prep := syntax.Preprocess([]byte(src))
	start, _ := syn.Parse([]byte(src), prep.Removed)
	first, _ := Resolve([]byte(src), start)
	second, _ := Resolve([]byte(src), start)
	require.Equal(t, first, second)
	require.Len(t, second.Periods, 1)
}

func TestHTMLSerialisationIsNotReproduced(t *testing.T) {
	m, ds := resolve("timeline\ntitle a & b<br>c\n")
	require.Empty(t, ds)
	require.Equal(t, "a & b<br>c", m.TitleLabel)
	m, ds = resolve("timeline\ntitle \u00a0<br>x\n")
	require.Empty(t, ds)
	require.Equal(t, "\u00a0<br>x", m.Title)
	m, ds = resolve("timeline\ntitle a<b\n")
	require.Empty(t, ds)
	require.Equal(t, "a<b", m.Title)
	m, ds = resolve("timeline\naccDescr {\na\n\u00a0<br>b\n}\n")
	require.Empty(t, ds)
	require.Equal(t, "a\n<br>b", m.AccDescr)
	m, ds = resolve("timeline\naccDescr: a\u00a0<br>b\n")
	require.Empty(t, ds)
	require.Equal(t, "a\u00a0<br>b", m.AccDescr)
}

func TestBareCommentLineNeverBecomesPayload(t *testing.T) {
	m, ds := resolve("timeline\na:\n%%\nb\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"|a|b"}, outline(m))
	m, ds = resolve("timeline\na:\n\n%%\nb\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"|a|b"}, outline(m))
	m, ds = resolve("timeline\ntitle\n%%\nx\n")
	require.Empty(t, ds)
	require.Equal(t, "x", m.Title)
	m, ds = resolve("timeline\naccDescr {\na\n%%\nb\n}\n")
	require.Empty(t, ds)
	require.Equal(t, "a\nb", m.AccDescr)
	for src, code := range map[string]string{
		"timeline\na :\n%%":           "timeline/unknown-statement",
		"timeline\naccTitle:\n\t%%":   "timeline/unexpected-token",
		"timeline\naccDescr:\n%%":     "timeline/unexpected-token",
		"timeline\naccDescr:\n\n%%\n": "timeline/unexpected-token",
	} {
		_, ds = resolve(src)
		require.Len(t, ds, 1, src)
		require.Equal(t, code, ds[0].Code, src)
	}
}
