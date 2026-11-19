package syntax

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/stretchr/testify/require"
)

const (
	ruleMalformed     = "malformed config value"
	ruleInvalidEscape = "invalid escape"
	ruleMultiDocument = "multi-document streams are not supported"
	ruleTabIndent     = "tab in indentation"
	parentColumn      = 0
	ownerColumn       = 2
)

func ruleRead(src string) (ConfigValue, []diag.Diagnostic) {
	return ParseConfigYAML([]byte(src), 0, len(src))
}

func ruleTokenEnd(src string, p int) int {
	if p >= len(src) {
		return len(src)
	}
	switch src[p] {
	case '\r':
		if p+1 < len(src) && src[p+1] == '\n' {
			return p + 2
		}
		return p + 1
	case ' ', '\t', '\n':
		return p + 1
	}
	end := p
	for end < len(src) && !strings.ContainsRune(" \t\r\n", rune(src[end])) {
		end++
	}
	return end
}

func requireRuleDiagnostic(t *testing.T, src string, ds []diag.Diagnostic, message string, start int) {
	t.Helper()
	require.Len(t, ds, 1, "input %q", src)
	require.Equal(t, "config/malformed", ds[0].Code, "input %q", src)
	require.Equal(t, message, ds[0].Message, "input %q", src)
	require.Equal(t, span(start, ruleTokenEnd(src, start)), ds[0].Span, "input %q", src)
}

func escapeWidth(src string, i int) int {
	if i+1 >= len(src) {
		return 0
	}
	switch src[i+1] {
	case '"', '\\', '/', 'b', 'f', 'n', 'r', 't', '\n':
		return 2
	case 'u':
		if i+6 <= len(src) && isHex4(src[i+2:i+6]) {
			return 6
		}
	}
	return 0
}

func isHex4(text string) bool {
	for i := range len(text) {
		if !strings.ContainsRune("0123456789abcdefABCDEF", rune(text[i])) {
			return false
		}
	}
	return true
}

type tailOutcome struct {
	closed     bool
	message    string
	start, end int
}

func quotedTailOutcome(src string, open int) tailOutcome {
	quote := src[open]
	for i := open + 1; i < len(src); {
		c := src[i]
		switch {
		case c == quote && quote == '\'' && i+1 < len(src) && src[i+1] == '\'':
			i += 2
		case c == quote:
			return tailOutcome{closed: true}
		case c == '\\' && quote == '"':
			width := escapeWidth(src, i)
			if width == 0 {
				return tailOutcome{message: ruleInvalidEscape, start: i, end: min(i+2, len(src))}
			}
			i += width
		default:
			i++
		}
	}
	return tailOutcome{message: ruleMalformed, start: len(src), end: len(src)}
}

type truncatedInput struct {
	src  string
	open int
}

func truncationsOf(prefix, scalar string) []truncatedInput {
	var inputs []truncatedInput
	for cut := 1; cut < len(scalar); cut++ {
		for _, tail := range []string{"", "\n"} {
			inputs = append(inputs, truncatedInput{prefix + scalar[:cut] + tail, len(prefix)})
		}
	}
	return inputs
}

func quotedTruncations() []truncatedInput {
	prefixes := []string{"a: ", "a:\n  ", "a: 1\nb: ", "k:\n  a:\n    ", "a:\n  - ", "config:\n  mindmap:\n    "}
	scalars := []string{
		`"colorBy: depth"`,
		`'colorBy: depth'`,
		`"esc \" q: \\ \u00e9 end"`,
		`'it''s: ok'`,
		"\"multi\n    line: two\"",
		"'one\n\n    two'",
	}
	var inputs []truncatedInput
	for _, prefix := range prefixes {
		for _, scalar := range scalars {
			inputs = append(inputs, truncationsOf(prefix, scalar)...)
		}
	}
	return inputs
}

func TestConfigQuotedValueTruncation(t *testing.T) {
	inputs := quotedTruncations()
	require.Greater(t, len(inputs), 1000)
	for _, in := range inputs {
		_, ds := ruleRead(in.src)
		outcome := quotedTailOutcome(in.src, in.open)
		if outcome.closed {
			require.Empty(t, ds, "input %q", in.src)
			continue
		}
		require.Len(t, ds, 1, "input %q", in.src)
		require.Equal(t, "config/malformed", ds[0].Code, "input %q", in.src)
		require.Equal(t, outcome.message, ds[0].Message, "input %q", in.src)
		require.Equal(t, span(outcome.start, outcome.end), ds[0].Span, "input %q", in.src)
	}
}

func quotedKeysFollowedByNonColon() []string {
	var keys []string
	for _, quote := range []string{`"`, `'`} {
		for _, prefix := range []string{"a: 1\n", ""} {
			keys = append(keys, prefix+quote+"k: b"+quote)
		}
	}
	var tails []string
	for _, gap := range []string{"", " ", " \t"} {
		for _, next := range "x7-.," {
			tails = append(tails, gap+string(next)+"\n")
		}
	}
	var inputs []string
	for _, key := range keys {
		for _, tail := range tails {
			inputs = append(inputs, key+tail)
		}
	}
	return inputs
}

func TestConfigQuotedKeyFollowedByNonColon(t *testing.T) {
	inputs := quotedKeysFollowedByNonColon()
	require.Len(t, inputs, 60)
	for _, src := range inputs {
		_, ds := ruleRead(src)
		requireRuleDiagnostic(t, src, ds, ruleMalformed, len(src)-2)
	}
}

func TestConfigNextLinePlainValueColumn(t *testing.T) {
	head := "k:\n  a:\n      plain\n"
	for column := 0; column <= 8; column++ {
		src := head + strings.Repeat(" ", column) + "more\n"
		value, ds := ruleRead(src)
		switch {
		case column > ownerColumn:
			require.Empty(t, ds, "input %q", src)
			require.Equal(t, "plain more", value.Entries[0].Value.Entries[0].Value.Text, "input %q", src)
		case column > parentColumn && column < ownerColumn:
			requireRuleDiagnostic(t, src, ds, ruleMalformed, len(head)+column)
		default:
			requireRuleDiagnostic(t, src, ds, ruleMalformed, len(src)-1)
		}
	}
}

func TestConfigNextLineFlowValueColumn(t *testing.T) {
	for _, c := range []struct{ head, line string }{
		{"k:\n  a:\n      [1,\n", "2]\n"},
		{"k:\n  a:\n      { \"k\": 1,\n", "\"m\": 2 }\n"},
	} {
		for column := 0; column <= 8; column++ {
			src := c.head + strings.Repeat(" ", column) + c.line
			_, ds := ruleRead(src)
			if column > ownerColumn {
				require.Empty(t, ds, "input %q", src)
				continue
			}
			requireRuleDiagnostic(t, src, ds, ruleMalformed, len(c.head)+column)
		}
	}
}

func TestConfigKeylessLineFailsAtLineEnd(t *testing.T) {
	for _, tail := range []string{"", " # c", "   # c  ", "  ", "\t"} {
		for _, end := range []string{"\n", ""} {
			src := "a: 1\nb" + tail + end
			_, ds := ruleRead(src)
			requireRuleDiagnostic(t, src, ds, ruleMalformed, len("a: 1\nb"+tail))
		}
	}
}

func TestConfigTabDuringContinuationProbe(t *testing.T) {
	for _, indent := range []string{"", " ", "  "} {
		src := "a: 1\na: 2\n" + indent + "\tb\n"
		tab := strings.IndexByte(src, '\t')
		_, ds := ruleRead(src)
		require.Len(t, ds, 1, "input %q", src)
		require.Equal(t, "config/malformed", ds[0].Code, "input %q", src)
		require.Equal(t, ruleTabIndent, ds[0].Message, "input %q", src)
		require.Equal(t, span(tab, tab+1), ds[0].Span, "input %q", src)
	}
}

type markerInput struct {
	src      string
	at       int
	boundary bool
}

func markerInputs(root, between, marker string) []markerInput {
	at := len(root) + 1 + len(between)
	var inputs []markerInput
	for _, term := range []string{"\n", " x\n", "\t", ""} {
		inputs = append(inputs, markerInput{root + "\n" + between + marker + term, at, true})
	}
	return append(inputs, markerInput{root + "\n" + between + marker + "x\n", at, false})
}

func TestConfigMarkerAfterRootValue(t *testing.T) {
	var inputs []markerInput
	for _, root := range []string{"'a'", `"a"`, "[a]", "{a: b}"} {
		for _, between := range []string{"", "\n", "# c\n", "  \n"} {
			for _, marker := range []string{"---", "..."} {
				inputs = append(inputs, markerInputs(root, between, marker)...)
			}
		}
	}
	require.Len(t, inputs, 160)
	for _, in := range inputs {
		_, ds := ruleRead(in.src)
		if !in.boundary {
			requireRuleDiagnostic(t, in.src, ds, ruleMalformed, in.at)
			continue
		}
		require.Len(t, ds, 1, "input %q", in.src)
		require.Equal(t, "config/malformed", ds[0].Code, "input %q", in.src)
		require.Equal(t, ruleMultiDocument, ds[0].Message, "input %q", in.src)
		require.Equal(t, span(in.at, in.at+3), ds[0].Span, "input %q", in.src)
	}
}

func TestConfigFlowValueInSequenceItem(t *testing.T) {
	value, ds := ruleRead("- {a: 1 b}\n- [x y]\n- {k: v}\n")
	require.Empty(t, ds)
	require.Len(t, value.Items, 3)
	require.Equal(t, ValueMapping, value.Items[0].Kind)
	require.Equal(t, "a", value.Items[0].Entries[0].Key)
	require.Equal(t, "1 b", value.Items[0].Entries[0].Value.Text)
	require.Equal(t, ValueSequence, value.Items[1].Kind)
	require.Equal(t, "x y", value.Items[1].Items[0].Text)
	require.Equal(t, ValueMapping, value.Items[2].Kind)
}

func TestConfigNodePrefixInsideFlowSequenceItem(t *testing.T) {
	for _, c := range []struct{ src, code, message, token string }{
		{"- {&a x: 1}\n", "config/unsupported-anchor", "anchors and aliases are not supported", "&a"},
		{"- [&a x]\n", "config/unsupported-anchor", "anchors and aliases are not supported", "&a"},
		{"- {!t x: 1}\n", "config/unsupported-tag", "tags are not supported", "!t"},
		{"- [!t x]\n", "config/unsupported-tag", "tags are not supported", "!t"},
	} {
		_, ds := ruleRead(c.src)
		at := strings.Index(c.src, c.token)
		require.Len(t, ds, 1, "input %q", c.src)
		require.Equal(t, c.code, ds[0].Code, "input %q", c.src)
		require.Equal(t, c.message, ds[0].Message, "input %q", c.src)
		require.Equal(t, span(at, at+len(c.token)), ds[0].Span, "input %q", c.src)
	}
}

func TestConfigNextLinePipeLineWithMapColon(t *testing.T) {
	for _, header := range []string{"|", ">"} {
		nested := "config:\n " + header + "\"k\": \"key\"\n"
		_, ds := ruleRead(nested)
		requireRuleDiagnostic(t, nested, ds, ruleMalformed, strings.Index(nested, header))
		mapLine := "a: 1\n" + header + "k: v\n"
		_, ds = ruleRead(mapLine)
		requireRuleDiagnostic(t, mapLine, ds, ruleMalformed, strings.Index(mapLine, header))
	}
}
