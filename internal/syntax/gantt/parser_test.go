package gantt

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func parse(src string) (*Start, []diag.Diagnostic) { return Parse([]byte(src), nil) }

func settingSummary(kind StatementKind) (string, bool) {
	switch n := kind.(type) {
	case *DateFormat:
		return "dateFormat=" + n.Token.Value, true
	case *InclusiveEndDates:
		return "inclusive", true
	case *TopAxis:
		return "topAxis", true
	case *AxisFormat:
		return "axisFormat=" + n.Token.Value, true
	case *TickInterval:
		return "tickInterval=" + n.Token.Value, true
	}
	return "", false
}

func calendarSummary(kind StatementKind) (string, bool) {
	switch n := kind.(type) {
	case *Excludes:
		return "excludes=" + n.Token.Value, true
	case *Includes:
		return "includes=" + n.Token.Value, true
	case *TodayMarker:
		return "todayMarker=" + n.Token.Value, true
	case *Weekday:
		return "weekday=" + n.Name, true
	case *Weekend:
		return "weekend=" + n.Name, true
	}
	return "", false
}

func textSummary(kind StatementKind) (string, bool) {
	switch n := kind.(type) {
	case *Title:
		return "title=" + n.Token.Value, true
	case *Section:
		return "section=" + n.Token.Value, true
	case *AccTitle:
		return "accTitle=" + n.Value.Value, true
	case *AccDescr:
		return "accDescr=" + n.Value.Value, true
	case *AccDescrBlock:
		return "block=" + n.Value.Value, true
	case *Task:
		return "task=" + n.Text.Value + "|" + n.Data.Value, true
	case *ClickStatement:
		return fmt.Sprintf("click=%s %v", n.Click.Value, n.Order), true
	}
	return "", false
}

func summary(start *Start) []string {
	var out []string
	for _, line := range start.Document.Lines {
		if line.Statement == nil {
			continue
		}
		for _, describe := range []func(StatementKind) (string, bool){settingSummary, calendarSummary, textSummary} {
			if text, ok := describe(line.Statement.Kind); ok {
				out = append(out, text)
			}
		}
	}
	return out
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code + ": " + d.Message
	}
	return out
}

func TestDirectivesAndTasks(t *testing.T) {
	start, ds := parse("gantt\n  title  My plan \n  dateFormat  YYYY-MM-DD\naxisFormat %d/%m\ntickInterval 1week\nexcludes weekends, 2014-01-10\nincludes 2014-01-11\ntodayMarker off\ninclusiveEndDates\ntopAxis\nweekday monday\nweekend friday\nsection Alpha\nDesign :a1, 2014-01-01, 30d\n  Build :after a1, 20d\n")
	require.Empty(t, ds)
	require.Equal(t, []string{
		"title= My plan ", "dateFormat= YYYY-MM-DD", "axisFormat=%d/%m", "tickInterval=1week",
		"excludes=weekends, 2014-01-10", "includes=2014-01-11", "todayMarker=off", "inclusive", "topAxis",
		"weekday=monday", "weekend=friday", "section=Alpha",
		"task=Design |:a1, 2014-01-01, 30d", "task=Build |:after a1, 20d",
	}, summary(start))
}

func TestKeywordsFoldCaseAndLackBoundaries(t *testing.T) {
	start, ds := parse("GANTT\nDATEFORMAT yyyy\nWeekday   Sunday\nTopAxisX\n")
	require.Equal(t, []string{"gantt/unexpected-token: unexpected \n, expected one of: taskData"}, codes(ds))
	require.Equal(t, []string{"dateFormat=yyyy", "weekday=sunday", "topAxis"}, summary(start))
}

func TestTaskTextBeginningWithCommandWordStartsMode(t *testing.T) {
	_, ds := parse("gantt\ncall me :a1, 2014-01-01, 3d\n")
	require.Equal(t, []string{"gantt/unterminated: unterminated call"}, codes(ds))
	start, ds := parse("gantt\ntitle plan\ntitle: x :a1, 2014-01-01, 3d\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"title=plan", "task=title|: x :a1, 2014-01-01, 3d"}, summary(start))
}

func TestTaskWithoutDataIsUnexpected(t *testing.T) {
	start, ds := parse("gantt\nlonely\nTask :a1, 2014-01-01, 3d\n")
	require.Equal(t, []string{"gantt/unexpected-token: unexpected \n, expected one of: taskData"}, codes(ds))
	require.Equal(t, []string{"task=Task |:a1, 2014-01-01, 3d"}, summary(start))
}

func TestUnknownStatements(t *testing.T) {
	start, ds := parse("gantt\n2014-01-01 release\n:\nsection S\n")
	require.Equal(t, []string{"gantt/unknown-statement: unknown statement 2014-01-01", "gantt/unknown-statement: unknown statement :"}, codes(ds))
	require.Equal(t, []string{"section=S"}, summary(start))
	require.Equal(t, 6, ds[0].Span.Start)
	require.Equal(t, 24, ds[0].Span.End)
}

func TestClickStatements(t *testing.T) {
	start, ds := parse("gantt\nclick a1 href \"http://x\" call fn(1, 2)\nclick a2 call go()\nclick a3 call fn(x) href \"y\"\n")
	require.Empty(t, ds)
	require.Equal(t, []string{
		"click=a1 [href callbackname callbackargs]", "click=a2 [callbackname]", "click=a3 [callbackname callbackargs href]",
	}, summary(start))
	first := start.Document.Lines[1].Statement.Kind.(*ClickStatement)
	require.Equal(t, "http://x", first.Href.Value)
	require.Equal(t, "fn", first.Callback.Value)
	require.Equal(t, "1, 2", first.Args.Value)
}

func TestClickWithoutCommandIsRejected(t *testing.T) {
	_, ds := parse("gantt\nclick a1\n")
	require.Equal(t, []string{"gantt/unexpected-token: unexpected end of input, expected one of: callbackname, href"}, codes(ds))
	_, ds = parse("gantt\nclick")
	require.Equal(t, []string{"gantt/unexpected-token: unexpected end of input, expected one of: callbackname, href"}, codes(ds))
}

func TestUnterminatedDelimiters(t *testing.T) {
	for src, want := range map[string]string{
		"gantt\nclick a href \"http://x":    "gantt/unterminated: unterminated \"",
		"gantt\nclick a call fn(1, 2":       "gantt/unterminated: unterminated (",
		"gantt\naccDescr {\nnever closed":   "gantt/unterminated: unterminated {",
		"gantt\nclick a call fn\nsection s": "gantt/unterminated: unterminated call",
	} {
		_, ds := parse(src)
		require.Equal(t, []string{want}, codes(ds), src)
	}
}

func TestAccessibility(t *testing.T) {
	start, ds := parse("gantt\naccTitle: A title\naccDescr: one\naccDescr {\n line a\n line b\n}\nsection s\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"accTitle=A title", "accDescr=one", "block=line a\n line b\n", "section=s"}, summary(start))
}

func TestCommentsAndSpansAfterRemoval(t *testing.T) {
	start, ds := parse("gantt\n%% note\n  %x\nsection s\n")
	require.Empty(t, ds)
	require.Equal(t, []string{"section=s"}, summary(start))
	stmt := start.Document.Lines[len(start.Document.Lines)-2].Statement
	require.NotNil(t, stmt)
	require.Equal(t, 19, stmt.Span.Start)
}

func TestSemicolonEndsDataButNotStatement(t *testing.T) {
	start, ds := parse("gantt\nTask :a1, 2014-01-01, 3d ; trailing\n")
	require.Equal(t, []string{"gantt/unexpected-token: unexpected \n, expected one of: taskData"}, codes(ds))
	require.Equal(t, []string{"task=Task |:a1, 2014-01-01, 3d "}, summary(start))
}
