package syntax

import (
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/stretchr/testify/require"
)

type diagWant struct {
	code    string
	message string
	span    source.Span
}

func requireDiags(t *testing.T, got []diag.Diagnostic, want []diagWant) {
	t.Helper()
	require.Len(t, got, len(want))
	for i, w := range want {
		require.Equal(t, w.code, got[i].Code, "diagnostic %d code", i)
		require.Equal(t, w.message, got[i].Message, "diagnostic %d message", i)
		require.Equal(t, w.span, got[i].Span, "diagnostic %d span", i)
		require.Equal(t, diag.SeverityError, got[i].Severity, "diagnostic %d severity", i)
		require.Empty(t, got[i].Help, "diagnostic %d help", i)
	}
}

func span(start, end int) source.Span {
	return source.Span{Start: start, End: end}
}

func TestConfigBlockScalarIndentationTabReportedOnce(t *testing.T) {
	src := []byte("a: |\n  x\n\t")
	_, diagnostics := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, diagnostics, []diagWant{{codeMalformed, msgTabIndent, span(9, 10)}})
}

func TestConfigRootFlowTrailingTab(t *testing.T) {
	src := []byte("{}\t")
	value, diagnostics := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, diagnostics)
	require.Equal(t, ValueMapping, value.Kind)
	require.Empty(t, value.Entries)
}

func TestConfigTabInIndentation(t *testing.T) {
	src := []byte("a: 1\n\tb: 2\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgTabIndent, span(5, 6)}})
}

func TestConfigBlockSequence(t *testing.T) {
	src := []byte("a: - b\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgBlockSequence, span(3, 4)}})
}

func TestConfigComplexKey(t *testing.T) {
	src := []byte("a: ? b\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgComplexKey, span(3, 4)}})
}

func TestConfigMultiDocument(t *testing.T) {
	src := []byte("a: 1\n---\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMultiDocument, span(5, 8)}})
}

func TestConfigMultiDocumentPlacedLater(t *testing.T) {
	src := []byte("a: 1\nb: 2\n...\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMultiDocument, span(10, 13)}})
}

func TestConfigBlockIndentIndicator(t *testing.T) {
	src := []byte("a: |2\n  x\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgBlockIndent, span(4, 5)}})
}

func TestConfigInvalidEscape(t *testing.T) {
	src := []byte("a: \"x\\q\"\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgInvalidEscape, span(5, 7)}})
}

func TestConfigInvalidEscapeAtRangeEnd(t *testing.T) {
	src := []byte("a: \"x\\")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgInvalidEscape, span(5, 6)}})
}

func TestConfigSurrogateEscapeYAML(t *testing.T) {
	src := []byte("a: \"\\ud800\"\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgUnicodeEscape, span(4, 10)}})
}

func TestConfigSurrogateEscapeYAMLRejectsPairing(t *testing.T) {
	src := []byte("a: \"\\ud800\\udc00\"\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgUnicodeEscape, span(4, 10)}})
}

func TestConfigSurrogateEscapeJSONLone(t *testing.T) {
	src := []byte("{\"a\": \"\\ud800\"}")
	_, ds := ParseConfigJSON(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgUnicodeEscape, span(7, 13)}})
}

func TestConfigDuplicateKey(t *testing.T) {
	src := []byte("a: 1\na: 2\n")
	value, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgDuplicateKey, span(5, 6)}})
	require.Len(t, value.Entries, 1)
	require.Equal(t, span(0, 1), value.Entries[0].KeySpan)
	require.Equal(t, "2", value.Entries[0].Value.Text)
}

func TestConfigDuplicateKeyJSON(t *testing.T) {
	src := []byte("{\"a\": 1, \"a\": 2}")
	_, ds := ParseConfigJSON(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgDuplicateKey, span(9, 12)}})
}

func TestConfigFrontmatterConfigNotMapping(t *testing.T) {
	src := []byte("---\nconfig: 5\n---\nflowchart\n")
	p := Preprocess(src)
	requireDiags(t, p.Diags, []diagWant{{codeMalformed, msgFrontmatterMap, span(12, 13)}})
	require.False(t, p.HasConfig)
}

func TestConfigDirectiveMalformedForm(t *testing.T) {
	src := []byte("%%{init x}%%\nflowchart\n")
	p := Preprocess(src)
	requireDiags(t, p.Diags, []diagWant{{codeMalformed, msgDirective, span(0, 3)}})
	require.Empty(t, p.Directives)
}

func TestConfigDirectiveUnclosed(t *testing.T) {
	src := []byte("%%{init: {\"a\":1}\nflowchart\n")
	p := Preprocess(src)
	requireDiags(t, p.Diags, []diagWant{{codeMalformed, msgDirective, span(0, 3)}})
	require.Equal(t, span(0, len(src)), p.Removed[0])
}

func TestConfigWrapWithBody(t *testing.T) {
	src := []byte("%%{wrap: 1}%%\nflowchart\n")
	p := Preprocess(src)
	requireDiags(t, p.Diags, []diagWant{{codeMalformed, msgWrapBody, span(0, 3)}})
	require.False(t, p.Wrap)
}

func TestConfigDirectiveBodyNotObject(t *testing.T) {
	src := []byte("%%{init: [1]}%%\nflowchart\n")
	p := Preprocess(src)
	requireDiags(t, p.Diags, []diagWant{{codeMalformed, msgDirectiveBody, span(9, 12)}})
}

func TestConfigMalformedValueTokenRule(t *testing.T) {
	src := []byte("a: 1\nb\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(6, 7)}})
}

func TestConfigMalformedValueTokenRuleAtEnd(t *testing.T) {
	src := []byte("a: 1\nb:")
	_, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
}

func TestConfigMalformedValueTokenRuleTakesRun(t *testing.T) {
	src := []byte("a: @tag more\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(3, 7)}})
}

func TestConfigAnchor(t *testing.T) {
	src := []byte("a: &x 1\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeAnchor, msgAnchor, span(3, 5)}})
}

func TestConfigAlias(t *testing.T) {
	src := []byte("a: *x-1\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeAnchor, msgAnchor, span(3, 7)}})
}

func TestConfigTag(t *testing.T) {
	src := []byte("a: !foo bar\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeTag, msgTag, span(3, 7)}})
}

func TestConfigTagStopsAtComma(t *testing.T) {
	src := []byte("a: !x,1\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeTag, msgTag, span(3, 5)}})
}

func TestConfigNestingDepth(t *testing.T) {
	src := []byte("a: " + strings.Repeat("[", 65) + strings.Repeat("]", 65) + "\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeDepth, msgDepth, span(66, 67)}})
}

func TestConfigNestingDepthJSON(t *testing.T) {
	body := strings.Repeat("[", 65) + strings.Repeat("]", 65)
	src := []byte("{\"a\": " + body + "}")
	_, ds := ParseConfigJSON(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeDepth, msgDepth, span(69, 70)}})
}

func TestConfigNestingDepthAt64(t *testing.T) {
	src := []byte("a: " + strings.Repeat("[", 63) + strings.Repeat("]", 63) + "\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
}

func TestConfigInvalidUTF8YAML(t *testing.T) {
	src := []byte("a: \xff\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeInvalidUTF8, "invalid UTF-8 at byte 3", span(3, 4)}})
}

func TestConfigDiagnosticsUseOrigin(t *testing.T) {
	src := []byte("xx" + "a: 1\na: 2\n" + "yy")
	_, ds := ParseConfigYAML(src, 2, 12)
	requireDiags(t, ds, []diagWant{{codeMalformed, msgDuplicateKey, span(7, 8)}})
}

func TestConfigMalformedTokenSpanIsRun(t *testing.T) {
	src := []byte("a: [1] xx\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(7, 9)}})
}

func TestConfigJSONTrailingGarbage(t *testing.T) {
	src := []byte("{\"a\": 1} x")
	_, ds := ParseConfigJSON(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(9, 10)}})
}

func TestConfigJSONRejectsArrayRoot(t *testing.T) {
	src := []byte("[1,2]")
	_, ds := ParseConfigJSON(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(0, 5)}})
}

func TestSettledReadingsRootBlockHeader(t *testing.T) {
	src := []byte("|\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(0, 1)}})
}

func TestSettledReadingsRootBlockHeaderFolded(t *testing.T) {
	src := []byte(">")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(0, 1)}})
}

func TestSettledReadingsRootBlockHeaderIndented(t *testing.T) {
	src := []byte("  >\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(2, 3)}})
}

func TestSettledReadingsRootIndentIsNotContent(t *testing.T) {
	src := []byte("  c0\n")
	value, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, ValueString, value.Kind)
	require.Equal(t, "c0", value.Text)
}

func TestSettledReadingsMarkerAtColumnZeroOnly(t *testing.T) {
	src := []byte("  ---\n")
	value, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, ValueString, value.Kind)
	require.Equal(t, "---", value.Text)
}

func TestSettledReadingsDashKeyIsEntry(t *testing.T) {
	src := []byte("-x:\n")
	value, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	require.Len(t, value.Entries, 1)
	require.Equal(t, "-x", value.Entries[0].Key)
	require.Equal(t, ValueNull, value.Entries[0].Value.Kind)
}

func TestSettledReadingsLeadingMapColonIsMalformed(t *testing.T) {
	src := []byte(": v\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(0, 1)}})
}

func TestSettledReadingsMapColonNeedsSeparator(t *testing.T) {
	src := []byte("a:b\n")
	value, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, ValueString, value.Kind)
	require.Equal(t, "a:b", value.Text)
}

func TestSettledReadingsMapColonAtRangeEnd(t *testing.T) {
	src := []byte("a:")
	value, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	require.Len(t, value.Entries, 1)
	require.Equal(t, "a", value.Entries[0].Key)
}

func TestSettledReadingsQuotedKeyNeedsMapColon(t *testing.T) {
	src := []byte("\"k\":v\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(3, 5)}})
}

func TestSettledReadingsTrailingDashIsNullSequence(t *testing.T) {
	value, ds := ParseConfigYAML([]byte("-"), 0, 1)
	require.Empty(t, ds)
	require.Equal(t, ValueSequence, value.Kind)
	require.Len(t, value.Items, 1)
	require.Equal(t, ValueNull, value.Items[0].Kind)

	value, ds = ParseConfigYAML([]byte("?"), 0, 1)
	require.Empty(t, ds)
	require.Equal(t, ValueString, value.Kind)
	require.Equal(t, "?", value.Text)
}

func TestSettledReadingsFlowFirstFailurePosition(t *testing.T) {
	src := []byte("a: [1, @]\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(7, 9)}})
}

func TestSettledReadingsCommentLineIndent(t *testing.T) {
	tail := yamlValue(t, "a: 1 # tail\n  # note\n", "a")
	require.Equal(t, "1", tail.Text)
	percent := Preprocess([]byte("\t%% tabbed\nflowchart\n"))
	require.Empty(t, percent.Diags)
	require.Equal(t, []source.Span{span(0, 11)}, percent.Removed)
}

func TestSettledReadingsFlowPlainKeepsSpaces(t *testing.T) {
	value := yamlValue(t, "a: [x y]\n", "a")
	require.Equal(t, ValueSequence, value.Kind)
	require.Len(t, value.Items, 1)
	require.Equal(t, ValueString, value.Items[0].Kind)
	require.Equal(t, "x y", value.Items[0].Text)
}

func TestSettledReadingsFlowPlainKeepsTab(t *testing.T) {
	value := yamlValue(t, "a: [x\ty]\n", "a")
	require.Equal(t, "x\ty", value.Items[0].Text)
}

func TestSettledReadingsFlowPlainStopsAtMapColon(t *testing.T) {
	src := []byte("a: [x:y]\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(5, 8)}})
}

func TestSettledReadingsColonAfterCommentStartsNothing(t *testing.T) {
	value, ds := ParseConfigYAML([]byte("x #: y\n"), 0, 9)
	require.Empty(t, ds)
	require.Equal(t, ValueString, value.Kind)
	require.Equal(t, "x", value.Text)
}

func TestSettledReadingsMapColonBeforeCommentStaysEntry(t *testing.T) {
	value := yamlValue(t, "x : # note\n", "x")
	require.Equal(t, ValueNull, value.Kind)
}

func TestSettledReadingsRootMapColonInsideBraceIsText(t *testing.T) {
	src := []byte("a{b : \n")
	value, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, ValueMapping, value.Kind)
	require.Len(t, value.Entries, 1)
	require.Equal(t, "a{b", value.Entries[0].Key)
	require.Equal(t, ValueNull, value.Entries[0].Value.Kind)
}

func TestSettledReadingsFlowPlainKeepsHash(t *testing.T) {
	value := yamlValue(t, "a: [x#y]\n", "a")
	require.Equal(t, "x#y", value.Items[0].Text)
}
