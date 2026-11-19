package state_test

import (
	"testing"
	"unicode/utf8"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	model "github.com/gosuda/elegant-mermaid/internal/model/state"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/state"
)

func resolved(t *testing.T, src string) (*model.Model, []diag.Diagnostic) {
	t.Helper()
	start, ds := parser.Parse([]byte(src), nil)
	require.Empty(t, ds)
	return model.Resolve([]byte(src), start)
}

func ids(states []model.State) []string {
	out := make([]string, 0, len(states))
	for _, s := range states {
		out = append(out, s.ID)
	}
	return out
}

func values(texts []model.Text) []string {
	out := make([]string, 0, len(texts))
	for _, t := range texts {
		out = append(out, t.Value)
	}
	return out
}

func TestRepeatedDefinitionsKeepIdentityTypeAndFirstBody(t *testing.T) {
	m, ds := resolved(t, "stateDiagram-v2\nA: first\nstate A <<fork>>\nstate A {\n B\n}\nstate A {\n C\n}\nA: second\n")
	require.Equal(t, []string{"A", "B"}, ids(m.States))
	require.Equal(t, model.KindDefault, m.States[0].Kind)
	require.Equal(t, []string{"first", "second"}, values(m.States[0].Descriptions))
	require.Equal(t, model.Parent{Kind: model.ParentState, Index: 0}, m.States[1].Parent)
	require.Len(t, ds, 1)
	require.Equal(t, m.States[0].Descriptions[1].Span, ds[0].Span)
}

func TestGeneratedIDsReuseRawIdentityAndKeepEndpointRoles(t *testing.T) {
	m, ds := resolved(t, "stateDiagram-v2\nstate root_start <<fork>>\n[*] --> A\nA --> [*]\n[*] --> A\n")
	require.Empty(t, ds)
	require.Len(t, m.States, 3)
	require.Equal(t, model.KindFork, m.States[0].Kind)
	require.Equal(t, 0, m.Transitions[0].From.State)
	require.Equal(t, model.RoleStart, m.Transitions[0].From.Role)
	require.Equal(t, model.RoleEnd, m.Transitions[1].To.Role)
	require.Len(t, m.Transitions, 3)
	require.Equal(t, m.Transitions[0].To.State, m.Transitions[2].To.State)
}

func TestConcurrentRegionsKeepEmptySegmentsAndDelimiters(t *testing.T) {
	src := "stateDiagram-v2\nstate Box {\n--\nA\n--\n--\n}\n"
	m, ds := resolved(t, src)
	require.Empty(t, ds)
	require.Len(t, m.Regions, 4)
	counts := make([]int, 0, len(m.Regions))
	for _, r := range m.Regions {
		counts = append(counts, len(r.Children))
	}
	require.Equal(t, []int{0, 1, 0, 0}, counts)
	require.Len(t, m.States, 2)
	require.Equal(t, model.Parent{Kind: model.ParentRegion, Index: 1}, m.States[1].Parent)
	for _, r := range m.Regions[1:] {
		require.NotNil(t, r.Separator, r.ID)
		require.Equal(t, "--", src[r.Separator.Start:r.Separator.End])
	}
}

func TestOrdinaryIDsAreGlobalAndDirectionIsLocalLastWins(t *testing.T) {
	m, ds := resolved(t, "stateDiagram-v2\ndirection LR\nstate X {\n direction BT\n A\n direction RL\n}\nA: outside\ndirection TB\n")
	require.Empty(t, ds)
	require.Len(t, m.States, 2)
	require.Equal(t, "TB", m.Scopes[0].Direction)
	require.Equal(t, "RL", m.Scopes[1].Direction)
	require.Equal(t, "outside", m.States[1].Descriptions[0].Value)
}

func TestStylesRemainLiteralAndClassesAppend(t *testing.T) {
	m, ds := resolved(t, "stateDiagram-v2\nclassDef hot fill:#abc,color:red;\nclassDef hot stroke:#123;\nclass A,B hot\nA:::hot\nstyle A fill:#name;,color:blue;\nstyle A stroke:#456;\n")
	require.Empty(t, ds)
	require.Len(t, m.States[0].Classes, 2)
	require.Equal(t, "stroke:#456", m.States[0].Styles[0].Value)
	require.Len(t, m.ClassDefinitions[0].Styles, 3)
	require.Equal(t, "fill:red", m.ClassDefinitions[0].TextStyles[0].Value)
}

func TestNotesReplaceAndLinksDoNotCreateTargets(t *testing.T) {
	src := "stateDiagram-v2\nnote left of A: old\nnote right of A: new\nclick absent href \"https://example.test\"\naccTitle: first\naccTitle: last\naccDescr: detail\n"
	m, ds := resolved(t, src)
	require.Empty(t, ds)
	require.Len(t, m.States, 1)
	require.Equal(t, 1, m.States[0].Note)
	require.Equal(t, "new", m.Notes[1].Text.Value)
	require.Equal(t, "right of", m.Notes[1].Position)
	require.Equal(t, "absent", m.Links[0].Target)
	require.Equal(t, "last", m.Title())
	require.Equal(t, "detail", m.Description())
	for _, d := range m.Directives {
		require.True(t, d.Span.Start == len(src) || utf8.RuneStart(src[d.Span.Start]))
		require.LessOrEqual(t, d.Span.End, len(src))
	}
}

func TestAliasColonRulesAndTransitionSpansAreRetained(t *testing.T) {
	src := "stateDiagram-v2\nstate \"Label\" as A: body: ignored\nstate \"Group\" as B:full {\n [*] --> C: go\n C --> [*]\n}\n"
	m, ds := resolved(t, src)
	require.Empty(t, ds)
	require.Equal(t, "A", m.States[0].ID)
	require.Equal(t, "body", m.States[0].Descriptions[1].Value)
	require.Equal(t, "B:full", m.States[1].ID)
	require.Equal(t, "B:full_start", m.States[2].ID)
	require.NotNil(t, m.Transitions[0].Label)
	require.Equal(t, "go", m.Transitions[0].Label.Value)
	tr := m.Transitions[0]
	require.Equal(t, "[*]", src[tr.From.IDSpan.Start:tr.From.IDSpan.End])
	require.Equal(t, "-->", src[tr.ArrowSpan.Start:tr.ArrowSpan.End])
}

func TestAcceptedNoEffectFormsDoNotCreateStates(t *testing.T) {
	m, ds := resolved(t, "stateDiagram-v2\nstate Unused\nhide empty description\nscale 2 width\nnote \"floating\" as Ghost\n")
	require.Empty(t, ds)
	require.Empty(t, m.States)
	require.Empty(t, m.Notes)
	require.Len(t, m.Directives, 4)
}

func TestLastClickReplacesLinkWithoutImplicitlyCreatingState(t *testing.T) {
	m, ds := resolved(t, "stateDiagram-v2\nclick Missing \"https://first.test\" \"first\"\nclick Missing href \"mailto:last@example.test\"\n")
	require.Empty(t, ds)
	require.Empty(t, m.States)
	require.Len(t, m.Links, 1)
	require.Equal(t, "mailto:last@example.test", m.Links[0].URL.Value)
	require.Nil(t, m.Links[0].Tooltip)
}

func TestUnsafeClicksWarnEvenWhenSupersededAndKeepLiteralLinks(t *testing.T) {
	src := "stateDiagram-v2\nclick Missing \"javascript:first\" \" first tooltip \"\nclick Missing \" data:second \" \" final tooltip \"\nclick Other href \" HtTpS://example.test \"\n"
	m, ds := resolved(t, src)
	require.Empty(t, m.States)
	require.Len(t, m.Links, 2)
	require.Equal(t, " data:second ", m.Links[0].URL.Value)
	require.NotNil(t, m.Links[0].Tooltip)
	require.Equal(t, " final tooltip ", m.Links[0].Tooltip.Value)
	require.Equal(t, " HtTpS://example.test ", m.Links[1].URL.Value)
	require.Len(t, ds, 2)
	for i, rejected := range []string{"\"javascript:first\"", "\" data:second \""} {
		d := ds[i]
		require.Equal(t, "interaction/unsafe-url", d.Code)
		require.Equal(t, diag.SeverityWarning, d.Severity)
		require.Equal(t, "link URL is not allowed", d.Message)
		require.Equal(t, "Use an http, https, or mailto link.", d.Help)
		require.Equal(t, rejected, src[d.Span.Start:d.Span.End])
		require.Empty(t, d.Fixes)
	}
}
