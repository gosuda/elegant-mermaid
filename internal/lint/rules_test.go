package lint

import (
	"bytes"
	"strconv"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func lintResult(src string, cfg Config) Result {
	return Run(Analyze([]byte(src)), cfg)
}

func lineOf(src string, d diag.Diagnostic) int {
	return source.NewIndex([]byte(src)).Position(d.Span.Start).Line
}

func summarize(src string, ds []diag.Diagnostic) []string {
	var out []string
	for _, d := range ds {
		out = append(out, d.Code+":"+strconv.Itoa(lineOf(src, d)))
	}
	return out
}

func TestDuplicateIDs(t *testing.T) {
	src := "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n"
	res := lintResult(src, Config{})
	require.Len(t, res.Lint, 1)
	got := res.Lint[0]
	require.Equal(t, "flowchart/duplicate-ids", got.Code)
	require.Equal(t, diag.SeverityError, got.Severity)
	require.Equal(t, "Node id declared twice with different labels", got.Message)
	later := strings.Index(src, "A[Begin]")
	first := strings.Index(src, "A[Start]")
	require.Equal(t, source.Span{Start: later, End: later + 1}, got.Span)
	require.Equal(t, []diag.Related{{Span: source.Span{Start: first, End: first + 1}, Message: "first declared here"}}, got.Related)
	require.Empty(t, got.Fixes)
}

func TestDuplicateIDsDeclarations(t *testing.T) {
	cases := []struct {
		name string
		src  string
		want []string
	}{
		{"same label repeats", "flowchart LR\n  A[x] --> B\n  A[x] --> C\n", nil},
		{"bare references never conflict", "flowchart LR\n  A[x] --> B\n  A --> C\n", nil},
		{"entity decoded labels compare equal", "flowchart LR\n  A[x#38;y] --> B\n  A[x#amp;y] --> C\n", nil},
		{"bare first then two labels", "flowchart LR\n  A --> B\n  A[x] --> C\n  A[y] --> D\n", []string{"4"}},
		{"every later conflict reports", "flowchart LR\n  A[x] --> B\n  A[y] --> C\n  A[z] --> D\n", []string{"3", "4"}},
		{"same label after a conflict still compares with the first", "flowchart LR\n  A[x] --> B\n  A[y] --> C\n  A[x] --> D\n", []string{"3"}},
		{"graph keyword", "graph TD\n  A[x] --> B\n  A[y] --> C\n", []string{"3"}},
		{"other kinds do not run the rule", "sequenceDiagram\n  A->>B: hi\n", nil},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			var lines []string
			for _, d := range lintResult(c.src, Config{}).Lint {
				require.Equal(t, "flowchart/duplicate-ids", d.Code)
				lines = append(lines, strconv.Itoa(lineOf(c.src, d)))
			}
			require.Equal(t, c.want, lines)
		})
	}
}

func TestDuplicateIDsRelatedIsFirstLabelled(t *testing.T) {
	src := "flowchart LR\n  A --> B\n  A[x] --> C\n  A[y] --> D\n"
	res := lintResult(src, Config{})
	require.Len(t, res.Lint, 1)
	first := strings.Index(src, "A[x]")
	require.Equal(t, source.Span{Start: first, End: first + 1}, res.Lint[0].Related[0].Span)
}

func TestCommonRules(t *testing.T) {
	selectBoth := Config{Select: []string{"common/acc-title-missing", "common/acc-descr-missing"}}
	cases := []struct {
		name string
		src  string
		cfg  Config
		want []string
	}{
		{"off by default", "flowchart LR\n  A --> B\n", Config{}, nil},
		{"both missing", "flowchart LR\n  A --> B\n", selectBoth, []string{"common/acc-descr-missing:1", "common/acc-title-missing:1"}},
		{"title present", "flowchart LR\n  accTitle: Flow\n  A --> B\n", selectBoth, []string{"common/acc-descr-missing:1"}},
		{"descr line present", "flowchart LR\n  accDescr: What it shows\n  A --> B\n", selectBoth, []string{"common/acc-title-missing:1"}},
		{"descr block present", "flowchart LR\n  accDescr {\n    What it shows\n  }\n  A --> B\n", selectBoth, []string{"common/acc-title-missing:1"}},
		{"both present", "flowchart LR\n  accTitle: Flow\n  accDescr: What it shows\n  A --> B\n", selectBoth, nil},
		{"commented title does not count", "flowchart LR\n  %% accTitle: Flow\n  A --> B\n", Config{Select: []string{"common/acc-title-missing"}}, []string{"common/acc-title-missing:1"}},
		{"title needs its colon", "flowchart LR\n  accTitle Flow\n  A --> B\n", Config{Select: []string{"common/acc-title-missing"}}, []string{"common/acc-title-missing:1"}},
		{"unknown kind skips common rules", "nonsense\n", selectBoth, nil},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			require.Equal(t, c.want, summarizeCommon(c.src, lintResult(c.src, c.cfg).Lint))
		})
	}
}

func summarizeCommon(src string, ds []diag.Diagnostic) []string {
	var out []string
	for _, line := range summarize(src, ds) {
		if strings.HasPrefix(line, "common/") {
			out = append(out, line)
		}
	}
	return out
}

func TestAccessibilityRuleSpan(t *testing.T) {
	src := "flowchart LR\n  A --> B\n"
	res := lintResult(src, Config{Select: []string{"common/acc-title-missing"}})
	require.Len(t, res.Lint, 1)
	d := res.Lint[0]
	require.Equal(t, source.Span{Start: 0, End: len("flowchart")}, d.Span)
	require.Equal(t, diag.SeverityWarning, d.Severity)
	require.Equal(t, "diagram has no accTitle line", d.Message)
	require.Equal(t, "Add an accTitle line that names the diagram.", d.Help)
}

func TestNoExperimental(t *testing.T) {
	src := "block-beta\n  columns 1\n"
	res := lintResult(src, Config{})
	var found []diag.Diagnostic
	for _, d := range res.Lint {
		if d.Code == "common/no-experimental" {
			found = append(found, d)
		}
	}
	require.Len(t, found, 1)
	require.Equal(t, "block-beta is a beta diagram type", found[0].Message)
	require.Equal(t, diag.SeverityWarning, found[0].Severity)
	require.Equal(t, source.Span{Start: 0, End: len("block-beta")}, found[0].Span)
	require.Empty(t, summarizeNoExperimental(lintResult("flowchart LR\n  A --> B\n", Config{}).Lint))
}

func summarizeNoExperimental(ds []diag.Diagnostic) []string {
	var out []string
	for _, d := range ds {
		if d.Code == "common/no-experimental" {
			out = append(out, d.Code)
		}
	}
	return out
}

func TestRunSeparatesSyntaxAndLint(t *testing.T) {
	src := "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n"
	res := lintResult(src, Config{})
	require.Empty(t, res.Syntax)
	require.Len(t, res.Lint, 1)
	require.Equal(t, res.Lint, res.All())
}

func TestRunSeverityOverride(t *testing.T) {
	src := "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n"
	res := lintResult(src, Config{Severity: map[string]diag.Severity{"flowchart/duplicate-ids": diag.SeverityInfo}})
	require.Len(t, res.Lint, 1)
	require.Equal(t, diag.SeverityInfo, res.Lint[0].Severity)
	require.Empty(t, lintResult(src, Config{Off: []string{"flowchart/duplicate-ids"}}).Lint)
	require.Empty(t, lintResult(src, Config{Ignore: []string{"flowchart/duplicate-ids"}}).Lint)
}

func TestLintSourceOrdersSyntaxAndLint(t *testing.T) {
	src := "flowchart LR\n  A -> B\n  A[x] --> C\n  A[y] --> D\n"
	report := LintSource([]byte(src), Config{})
	require.True(t, bytes.Equal([]byte(src), report.Source))
	require.True(t, len(report.Diagnostics) >= 2)
	for i := 1; i < len(report.Diagnostics); i++ {
		require.LessOrEqual(t, report.Diagnostics[i-1].Span.Start, report.Diagnostics[i].Span.Start)
	}
}
