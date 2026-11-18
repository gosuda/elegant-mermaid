package state

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func parse(t *testing.T, src string) (*Start, []diag.Diagnostic) {
	t.Helper()
	return Parse([]byte(src), nil)
}

func statements(doc Document) []*Statement {
	var out []*Statement
	for _, l := range doc.Lines {
		if l.Statement != nil {
			out = append(out, l.Statement)
		}
	}
	return out
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func node[T StatementNode](t *testing.T, s *Statement) T {
	t.Helper()
	n, ok := s.Node.(T)
	require.True(t, ok, "%T", s.Node)
	return n
}

func TestHeaderAcceptsEOFWithoutSyntheticLines(t *testing.T) {
	start, ds := parse(t, "stateDiagram-v2")
	require.Empty(t, ds)
	require.Empty(t, start.Document.Lines)
	require.Equal(t, "stateDiagram-v2", start.Header.Text)
	require.Equal(t, 15, start.Span.End)
}

func TestAliasKeepsBodyAndColonIdentifierDistinction(t *testing.T) {
	src := "stateDiagram\nstate \"First\" as a: detail\nstate \"Second\" as b: detail {\n[*] --> C\n}\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	ss := statements(start.Document)
	require.Len(t, ss, 2)
	first := node[*Composite](t, ss[0])
	require.Equal(t, "a: detail", strings.TrimSpace(first.ID.Text))
	require.Equal(t, "First", first.Description.Text)
	require.Nil(t, first.Body)
	second := node[*Composite](t, ss[1])
	require.Equal(t, "b: detail", strings.TrimSpace(second.ID.Text))
	require.NotNil(t, second.Body)
	require.Len(t, statements(*second.Body), 1)
	require.NotNil(t, second.Delimiters)
	require.Equal(t, "state \"Second\" as b: detail {\n[*] --> C\n}", src[ss[1].Span.Start:ss[1].Span.End])
}

func TestRejectsChainedTransitionAndRecoversInsideScope(t *testing.T) {
	start, ds := parse(t, "stateDiagram\nstate Outer {\nA --> B --> C\nD --> E\n}\nF\n")
	require.Equal(t, []string{"state/unexpected-token"}, codes(ds))
	ss := statements(start.Document)
	require.Len(t, ss, 2)
	outer := node[*Composite](t, ss[0])
	require.NotNil(t, outer.Body)
	children := statements(*outer.Body)
	require.Len(t, children, 1)
	tr := node[*Transition](t, children[0])
	require.Equal(t, [2]string{"D", "E"}, [2]string{tr.From.ID.Text, tr.To.ID.Text})
}

func TestQuotedDescriptionsAndBlockNotesRetainPhysicalLineEnds(t *testing.T) {
	start, ds := parse(t, "stateDiagram\rstate \"one\r\ntwo\rthree\" as A\rnote left of A\rfirst\r\nsecond\rend note\r")
	require.Empty(t, ds)
	ss := statements(start.Document)
	c := node[*Composite](t, ss[0])
	require.NotNil(t, c.Description)
	require.Equal(t, "one\r\ntwo\rthree", c.Description.Text)
	n := node[*Note](t, ss[1])
	require.Equal(t, "first\r\nsecond", n.Text.Text)
	require.Equal(t, "left_of", n.Position.Value)
	require.Equal(t, "A", n.Target.Text)
}

func TestDefaultClassDefKeepsAuthorityTokenMismatch(t *testing.T) {
	start, ds := parse(t, "stateDiagram\nclassDef default fill:red\nA\n")
	require.Equal(t, []string{"state/unexpected-token"}, codes(ds))
	require.Equal(t, "unexpected default , expected one of: CLASSDEF_ID, DEFAULT", ds[0].Message)
	require.Len(t, statements(start.Document), 1)
}

func TestStylesKeepOrderAndLiteralComponents(t *testing.T) {
	start, ds := parse(t, "stateDiagram\nclassDef marked fill:#abc,color:red;\nstyle B,A fill:blue,stroke:red;\nclass B,A marked\nA:::marked --> B: go\n")
	require.Empty(t, ds)
	ss := statements(start.Document)
	style := node[*StyleStatement](t, ss[1])
	require.Equal(t, "B,A", strings.TrimSpace(style.Targets.Text))
	require.Equal(t, "fill:blue,stroke:red;", style.Styles.Text)
	tr := node[*Transition](t, ss[3])
	require.NotNil(t, tr.From.CSSClass)
	require.Equal(t, "marked", tr.From.CSSClass.Text)
	require.NotNil(t, tr.Description)
	require.Equal(t, ": go", tr.Description.Text)
}

func TestCommentSplitAndSourceOrderAreObservable(t *testing.T) {
	tokens := lex("stateDiagram\nA%% comment\nnoise direction LR suffix\n", nil)
	var ids []string
	var direction *Token
	for i, tok := range tokens {
		if tok.Kind == "ID" {
			ids = append(ids, tok.Text)
		}
		if tok.Kind == "direction_lr" && direction == nil {
			direction = &tokens[i]
		}
	}
	require.Equal(t, []string{"A"}, ids)
	require.NotNil(t, direction)
	require.Equal(t, "noise direction LR suffix", direction.Text)
}

func TestAccessibilityBlockKeepsClosingDelimiterSpan(t *testing.T) {
	src := "stateDiagram\naccDescr {first\nsecond}\nA\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	s := statements(start.Document)[0]
	a := node[*Accessibility](t, s)
	require.False(t, a.Title)
	require.Equal(t, "first\nsecond", a.Value.Text)
	require.Equal(t, "accDescr {first\nsecond}", src[s.Span.Start:s.Span.End])
}

func TestUnclosedCompositeIsNotResolvedAsPartialState(t *testing.T) {
	start, ds := parse(t, "stateDiagram\nstate A {\nB\n")
	require.Equal(t, []string{"state/unterminated"}, codes(ds))
	require.Equal(t, 21, ds[0].Span.Start)
	require.Empty(t, statements(start.Document))
}

func TestNestingStopsBeforeLevelSixtyFive(t *testing.T) {
	var b strings.Builder
	b.WriteString("stateDiagram\n")
	for i := range 65 {
		fmt.Fprintf(&b, "state n%d {\n", i)
	}
	_, ds := parse(t, b.String())
	depth := 0
	for _, d := range ds {
		require.NotEqual(t, "state/unterminated", d.Code)
		if d.Code == "limit/nesting-depth" {
			depth++
			require.Equal(t, "Reduce the nesting to 64 levels or fewer.", d.Help)
		}
	}
	require.Equal(t, 1, depth)
}

func TestDirectivesAndSymbolAlternativesKeepTypedFacts(t *testing.T) {
	src := "stateDiagram\nstate f <<fork>>\nstate j [[join]]\nstate c <<choice>>\nstate Ignored\nnote \"memo\" as Float\nclick f \"https://example.com\" \"tip\"\nclick j href \"mailto:x@y\"\naccTitle: A\naccDescr: B\nscale 2 width\nhide empty description\nstate Outer {\n--\nA\n--\n}\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	ss := statements(start.Document)
	require.Len(t, ss, 12)
	type stereo struct {
		id   string
		kind StereotypeKind
	}
	var got []stereo
	for _, s := range ss {
		if st, ok := s.Node.(*Stereotype); ok {
			got = append(got, stereo{st.ID.Text, st.Kind})
		}
	}
	require.Equal(t, []stereo{{"f", StereotypeFork}, {"j", StereotypeJoin}, {"c", StereotypeChoice}}, got)
	fn := node[*FloatingNote](t, ss[4])
	require.Equal(t, "memo", fn.Text.Text)
	require.Equal(t, "Float", strings.TrimSpace(fn.ID.Text))
	click := node[*Click](t, ss[5])
	require.Equal(t, "https://example.com", click.URL.Text)
	require.NotNil(t, click.Tooltip)
	require.Equal(t, "tip", click.Tooltip.Text)
	require.Nil(t, node[*Click](t, ss[6]).Tooltip)
	outer := node[*Composite](t, ss[11])
	require.NotNil(t, outer.Body)
	concurrent := 0
	for _, s := range statements(*outer.Body) {
		if _, ok := s.Node.(*Concurrent); ok {
			concurrent++
		}
	}
	require.Equal(t, 2, concurrent)
}

func TestUnclosedQuotePointsAtQuoteAndPreservesUnicodeBoundaries(t *testing.T) {
	src := "stateDiagram\nstate \"unfinished é"
	start, ds := parse(t, src)
	require.Equal(t, []string{"state/unterminated"}, codes(ds))
	require.Equal(t, "\"unfinished é", src[ds[0].Span.Start:ds[0].Span.End])
	require.Empty(t, statements(start.Document))
}

func TestColonDescriptionAcceptsMultibyteScalarAfterPairedColon(t *testing.T) {
	start, ds := parse(t, "stateDiagram\nA: first:é\n")
	require.Empty(t, ds)
	id := node[*IDDeclaration](t, statements(start.Document)[0])
	require.NotNil(t, id.Description)
	require.Equal(t, ": first:é", id.Description.Text)
}

func TestCompositeOpensBraceOnNextLineKeepsChildrenAndSpans(t *testing.T) {
	src := "stateDiagram-v2\n\n  state Parent\n  {\n  Child\n  }\n\n  Parent --> Other : label\n"
	start, ds := parse(t, src)
	require.Empty(t, ds)
	ss := statements(start.Document)
	require.Len(t, ss, 2)
	c := node[*Composite](t, ss[0])
	require.Equal(t, "Parent", c.ID.Text)
	require.NotNil(t, c.Body)
	require.NotNil(t, c.Delimiters)
	require.Equal(t, "{", src[c.Delimiters.Open.Start:c.Delimiters.Open.End])
	require.Equal(t, "}", src[c.Delimiters.Close.Start:c.Delimiters.Close.End])
	children := statements(*c.Body)
	require.Len(t, children, 1)
	child := node[*IDDeclaration](t, children[0])
	require.Equal(t, "Child", child.ID.ID.Text)
	require.Equal(t, "Child", src[child.ID.Span.Start:child.ID.Span.End])
	require.Equal(t, "Child", src[children[0].Span.Start:children[0].Span.End])
	require.Equal(t, "state Parent\n  {\n  Child\n  }", src[ss[0].Span.Start:ss[0].Span.End])
	tr := node[*Transition](t, ss[1])
	require.Equal(t, [2]string{"Parent", "Other"}, [2]string{tr.From.ID.Text, tr.To.ID.Text})
	require.NotNil(t, tr.Description)
	require.Equal(t, ": label", tr.Description.Text)
}

func TestBlankLineBeforeBraceKeepsCompositeBareAndRejectsStrayBrace(t *testing.T) {
	start, ds := parse(t, "stateDiagram\nstate Parent\n\n{\nChild\n}\n")
	require.Equal(t, []string{"state/unknown-statement", "state/unexpected-token"}, codes(ds))
	for _, d := range ds {
		require.Equal(t, diag.SeverityError, d.Severity)
	}
	ss := statements(start.Document)
	require.Len(t, ss, 2)
	require.Nil(t, node[*Composite](t, ss[0]).Body)
	require.Equal(t, "Child", node[*IDDeclaration](t, ss[1]).ID.ID.Text)
}
