package lint

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	dup     = "flowchart/duplicate-ids"
	unknown = "meta/unknown-rule"
	unused  = "meta/unused-suppression"
	bad     = "meta/malformed-suppression"
)

func lines(parts ...string) string {
	return strings.Join(parts, "\n") + "\n"
}

func TestSuppression(t *testing.T) {
	head := "flowchart LR"
	first := "  A[Start] --> B[End]"
	second := "  A[Begin] --> C[End]"
	third := "  A[Third] --> D[End]"
	cases := []struct {
		name string
		src  string
		want []string
	}{
		{"next line covers the declaration below", lines(head, first, "%% emd-disable-next-line "+dup+": ids collide upstream", second), nil},
		{"next line tolerates leading blanks", lines(head, first, "\t  %% emd-disable-next-line "+dup+": r", second), nil},
		{"next line above the wrong line is unused", lines(head, "%% emd-disable-next-line "+dup+": r", first, second), []string{unused + ":2", dup + ":4"}},
		{"blank lines are not skipped", lines(head, first, "%% emd-disable-next-line "+dup+": r", "", second), []string{unused + ":3", dup + ":5"}},
		{"comment lines are not skipped", lines(head, first, "%% emd-disable-next-line "+dup+": r", "%% note", second), []string{unused + ":3", dup + ":5"}},
		{"next line on the last line covers nothing", lines(head, first, second) + "%% emd-disable-next-line " + dup + ": r", []string{dup + ":3", unused + ":4"}},
		{"disable and enable bound the scope", lines(head, first, "%% emd-disable "+dup+": r", second, "%% emd-enable "+dup, third), []string{dup + ":6"}},
		{"disable runs to the end of the block", lines(head, first, "%% emd-disable "+dup+": r", second, third), nil},
		{"disable closed before the declaration is unused", lines(head, first, "%% emd-disable "+dup+": r", "%% emd-enable "+dup, second), []string{unused + ":3", dup + ":5"}},
		{"diagram scope covers lines above the directive", lines(head, first, second, "%% emd-disable-diagram "+dup+": r"), nil},
		{"diagram scope covers lines below the directive", lines(head, "%% emd-disable-diagram "+dup+": r", first, second, third), nil},
		{"code list accepts one space after a comma", lines(head, first, "%% emd-disable-next-line "+dup+", common/no-experimental: r", second), nil},
		{"unknown code is reported and the rest applies", lines(head, first, "%% emd-disable-next-line "+dup+", flowchart/nope: r", second), []string{unknown + ":3"}},
		{"only unknown codes suppress nothing and stay quiet about it", lines(head, first, "%% emd-disable-next-line nope/nothing: r", second), []string{unknown + ":3", dup + ":4"}},
		{"unused directive names the codes", lines(head, first, "%% emd-disable-next-line "+dup+": r", "  C --> D"), []string{unused + ":3"}},
		{"missing reason is malformed", lines(head, first, "%% emd-disable-next-line "+dup, second), []string{bad + ":3", dup + ":4"}},
		{"empty reason is malformed", lines(head, first, "%% emd-disable-next-line "+dup+":   ", second), []string{bad + ":3", dup + ":4"}},
		{"empty code list is malformed", lines(head, first, "%% emd-disable-next-line : reason", second), []string{bad + ":3", dup + ":4"}},
		{"no code list at all is malformed", lines(head, first, "%% emd-disable-next-line", second), []string{bad + ":3", dup + ":4"}},
		{"wildcard is malformed", lines(head, first, "%% emd-disable-next-line flowchart/*: r", second), []string{bad + ":3", dup + ":4"}},
		{"blank before the colon is malformed", lines(head, first, "%% emd-disable-next-line "+dup+" : r", second), []string{bad + ":3", dup + ":4"}},
		{"two blanks after a comma are malformed", lines(head, first, "%% emd-disable-next-line "+dup+",  common/no-experimental: r", second), []string{bad + ":3", dup + ":4"}},
		{"trailing comma is malformed", lines(head, first, "%% emd-disable-next-line "+dup+",: r", second), []string{bad + ":3", dup + ":4"}},
		{"enable takes no reason", lines(head, first, "%% emd-disable "+dup+": r", "%% emd-enable "+dup+": done", second), []string{bad + ":4"}},
		{"enable without an open disable is malformed", lines(head, first, "%% emd-enable "+dup, second), []string{bad + ":3", dup + ":4"}},
		{"disable of an open code is malformed", lines(head, first, "%% emd-disable "+dup+": r", "%% emd-disable "+dup+": again", second), []string{bad + ":4"}},
		{"a malformed directive applies nothing", lines(head, first, "%% emd-disable-next-line "+dup+", meta/unknown-rule: r", second), []string{bad + ":3", dup + ":4"}},
		{"syntax error rows cannot be suppressed", lines(head, first, "%% emd-disable-next-line flowchart/arrow-invalid: r", second), []string{bad + ":3", dup + ":4"}},
		{"meta rows cannot be suppressed", lines(head, first, "%% emd-disable-next-line meta/unused-suppression: r", second), []string{bad + ":3", dup + ":4"}},
		{"other comments stay ordinary", lines(head, first, "%% emd-foo "+dup, "%%emd-disable-next-line "+dup+": r", second), []string{dup + ":5"}},
		{"a trailing comment is not a directive", lines(head, first, "  A[Begin] --> C[End] %% emd-disable-next-line "+dup+": r"), []string{dup + ":3"}},
		{"keyword prefix is not a directive", lines(head, first, "%% emd-disable-next-lines "+dup+": r", second), []string{dup + ":4"}},
		{"the disable-file form is a comment inside a block", lines(head, first, "%% emd-disable-file "+dup+": r", second), []string{dup + ":4"}},
		{"CRLF line endings", strings.ReplaceAll(lines(head, first, "%% emd-disable-next-line "+dup+": r", second), "\n", "\r\n"), nil},
		{"lone CR line endings", strings.ReplaceAll(lines(head, first, "%% emd-disable-next-line "+dup+": r", second), "\n", "\r"), nil},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			require.Equal(t, c.want, summarize(c.src, lintResult(c.src, Config{}).Lint))
		})
	}
}

func TestSuppressionDiagnosticDetails(t *testing.T) {
	src := lines("flowchart LR", "  A[Start] --> B[End]", "  %% emd-disable-next-line flowchart/duplicate-ids, flowchart/nope: r", "  A[Begin] --> C[End]")
	res := lintResult(src, Config{})
	require.Len(t, res.Lint, 1)
	d := res.Lint[0]
	token := strings.Index(src, "flowchart/nope")
	require.Equal(t, source.Span{Start: token, End: token + len("flowchart/nope")}, d.Span)
	require.Equal(t, "unknown rule flowchart/nope", d.Message)
	require.Equal(t, diag.SeverityWarning, d.Severity)
	require.Equal(t, "Use a code from the lint rule registry.", d.Help)

	src = lines("flowchart LR", "  %% emd-disable-next-line flowchart/duplicate-ids, common/no-experimental: r", "  A --> B")
	res = lintResult(src, Config{})
	require.Len(t, res.Lint, 1)
	d = res.Lint[0]
	start := strings.Index(src, "%% emd-disable")
	require.Equal(t, source.Span{Start: start, End: len(src) - len("  A --> B\n") - 1}, d.Span)
	require.Equal(t, "suppression of flowchart/duplicate-ids, common/no-experimental suppresses nothing", d.Message)
	require.Equal(t, "Remove the directive, or move it to the line it should cover.", d.Help)

	src = lines("flowchart LR", "  %% emd-disable-next-line", "  A --> B")
	res = lintResult(src, Config{})
	require.Len(t, res.Lint, 1)
	require.Equal(t, "malformed suppression directive", res.Lint[0].Message)
	start = strings.Index(src, "%% emd-disable")
	require.Equal(t, source.Span{Start: start, End: start + len("%% emd-disable-next-line")}, res.Lint[0].Span)
}

func TestSuppressionHonoursRuleConfig(t *testing.T) {
	src := lines("flowchart LR", "  %% emd-disable-next-line "+dup+": r", "  A --> B")
	require.Equal(t, []string{unused + ":2"}, summarize(src, lintResult(src, Config{}).Lint))
	info := lintResult(src, Config{Severity: map[string]diag.Severity{unused: diag.SeverityInfo}})
	require.Len(t, info.Lint, 1)
	require.Equal(t, diag.SeverityInfo, info.Lint[0].Severity)
	require.Empty(t, lintResult(src, Config{Ignore: []string{unused}}).Lint)
	require.Empty(t, lintResult(src, Config{Off: []string{unused}}).Lint)
	require.Empty(t, lintResult(src, Config{Select: []string{dup}}).Lint)

	selected := Config{Select: []string{"common/acc-title-missing"}}
	covered := lines("flowchart LR", "%% emd-disable-diagram common/acc-title-missing: no title wanted", "  A --> B")
	require.Empty(t, lintResult(covered, selected).Lint)
	require.Equal(t, []string{unused + ":2"}, summarize(covered, lintResult(covered, Config{}).Lint))
}

func TestSuppressionAppliesToSyntaxWarnings(t *testing.T) {
	src := lines("flowchart LR", "  A --> B", "%% emd-disable-next-line config/unknown-key: r", "  C --> D")
	third := strings.Index(src, "  C --> D")
	a := &Analysis{
		Source: []byte(src),
		Block:  Block{Source: []byte(src)},
		Syntax: []diag.Diagnostic{
			{Code: "config/unknown-key", Severity: diag.SeverityWarning, Span: source.Span{Start: third + 2, End: third + 3}},
			{Code: "common/unknown-diagram-kind", Severity: diag.SeverityError, Span: source.Span{Start: third + 2, End: third + 3}},
		},
	}
	res := Run(a, Config{})
	require.Len(t, res.Syntax, 1)
	require.Equal(t, "common/unknown-diagram-kind", res.Syntax[0].Code)
	require.Empty(t, res.Lint)
}

func TestSuppressionIgnoresDirectivesAboveTheBody(t *testing.T) {
	src := []byte(lines("%% emd-disable-next-line "+dup+": r", "flowchart LR"))
	dirs, finds := parseBlockDirectives(src, 0)
	require.Len(t, dirs, 1)
	require.Empty(t, finds)
	dirs, finds = parseBlockDirectives(src, len("%% emd-disable-next-line "+dup+": r\n"))
	require.Empty(t, dirs)
	require.Empty(t, finds)
}

func TestSuppressibleCodes(t *testing.T) {
	entry, ok := lookup(dup)
	require.True(t, ok)
	require.Equal(t, dup, entry.canonical)
	_, ok = lookup("flowchart/not-a-rule")
	require.False(t, ok)
	require.False(t, suppressibleCode("flowchart/not-a-rule"))
	require.True(t, suppressibleCode(dup))
	require.True(t, suppressibleCode("config/unknown-key"))
	require.False(t, suppressibleCode("flowchart/unclosed-node-bracket"))
	require.False(t, suppressibleCode("flowchart/arrow-invalid"))
	require.False(t, suppressibleCode("common/unknown-diagram-kind"))
	require.False(t, suppressibleCode(unknown))
}

const (
	hostDup = "flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]\n"
	hostTwo = "flowchart LR\n  X[a] --> Y\n  X[b] --> Z\n"
)

func hostWith(directive string) string {
	return "# Doc\n\n" + directive + "\n\n```mermaid\n" + hostDup + "```\n\ntext\n\n```mermaid\n" + hostTwo + "```\n"
}

func hostLint(host string, cfg Config) []string {
	return summarize(host, LintHost([]byte(host), cfg).Diagnostics)
}

func TestSuppressionFileDirective(t *testing.T) {
	dupA, dupB := dup+":8", dup+":16"
	require.Equal(t, []string{dupA, dupB}, hostLint(hostWith("no directive here"), Config{}))
	require.Empty(t, hostLint(hostWith("<!-- emd-disable-file "+dup+": legacy ids -->"), Config{}))
	require.Empty(t, hostLint(hostWith("<!-- emd-disable-file "+dup+", common/no-experimental: legacy ids -->"), Config{}))

	unusedHost := "<!-- emd-disable-file " + dup + ": r -->\n\n```mermaid\nflowchart LR\n  A --> B\n```\n"
	got := LintHost([]byte(unusedHost), Config{}).Diagnostics
	require.Equal(t, []string{unused + ":1"}, summarize(unusedHost, got))
	require.Equal(t, source.Span{Start: 0, End: strings.Index(unusedHost, "\n")}, got[0].Span)

	require.Equal(t, []string{bad + ":3", dupA, dupB}, hostLint(hostWith("<!-- emd-disable-file "+dup+" -->"), Config{}))
	require.Equal(t, []string{bad + ":3", dupA, dupB}, hostLint(hostWith("<!-- emd-disable-file "+dup+": reason"), Config{}))
	require.Equal(t, []string{bad + ":3", dupA, dupB}, hostLint(hostWith("<!-- emd-disable-file "+unknown+": r -->"), Config{}))
	require.Equal(t, []string{unknown + ":3"}, hostLint(hostWith("<!-- emd-disable-file "+dup+", flowchart/nope: r -->"), Config{}))
}

func TestSuppressionFileDirectiveSkipsFencedBlocks(t *testing.T) {
	host := "```md\n<!-- emd-disable-file " + dup + ": r -->\n```\n\n```mermaid\n" + hostDup + "```\n"
	require.Equal(t, []string{dup + ":8"}, hostLint(host, Config{}))

	tilde := "~~~~\n<!-- emd-disable-file " + dup + ": r -->\n~~~\n<!-- emd-disable-file " + dup + ": r -->\n~~~~\n\n```mermaid\n" + hostDup + "```\n"
	require.Equal(t, []string{dup + ":10"}, hostLint(tilde, Config{}))
}

func TestSuppressionFileDirectiveMapsHostPositions(t *testing.T) {
	host := hostWith("<!-- emd-disable-file common/acc-title-missing: r -->")
	report := LintHost([]byte(host), Config{})
	second := strings.Index(host, "A[Begin]")
	require.Len(t, report.Diagnostics, 3)
	require.Equal(t, unused, report.Diagnostics[0].Code)
	require.Equal(t, source.Span{Start: second, End: second + 1}, report.Diagnostics[1].Span)
	require.Equal(t, strings.Index(host, "A[Start]"), report.Diagnostics[1].Related[0].Span.Start)
}
