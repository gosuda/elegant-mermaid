package syntax

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/stretchr/testify/require"
)

func yamlValue(t *testing.T, src string, key string) ConfigValue {
	t.Helper()
	value, ds := ParseConfigYAML([]byte(src), 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, ValueMapping, value.Kind)
	i := findEntry(value, key)
	require.GreaterOrEqual(t, i, 0, "key %q missing", key)
	return value.Entries[i].Value
}

func TestBlockScalarLiteralClip(t *testing.T) {
	got := yamlValue(t, "a: |\n  one\n  two\n", "a")
	require.Equal(t, ValueString, got.Kind)
	require.Equal(t, "one\ntwo\n", got.Text)
}

func TestBlockScalarLiteralStrip(t *testing.T) {
	got := yamlValue(t, "a: |-\n  one\n  two\n\n\n", "a")
	require.Equal(t, "one\ntwo", got.Text)
}

func TestBlockScalarLiteralKeep(t *testing.T) {
	got := yamlValue(t, "a: |+\n  one\n\n\n", "a")
	require.Equal(t, "one\n\n\n", got.Text)
}

func TestBlockScalarLiteralBlankBetween(t *testing.T) {
	got := yamlValue(t, "a: |\n  one\n\n  two\n", "a")
	require.Equal(t, "one\n\ntwo\n", got.Text)
}

func TestBlockScalarFoldedClip(t *testing.T) {
	got := yamlValue(t, "a: >\n  one\n  two\n", "a")
	require.Equal(t, "one two\n", got.Text)
}

func TestBlockScalarFoldedStrip(t *testing.T) {
	got := yamlValue(t, "a: >-\n  x\n  y\n", "a")
	require.Equal(t, "x y", got.Text)
}

func TestBlockScalarFoldedBlankBetween(t *testing.T) {
	got := yamlValue(t, "a: >\n  one\n\n  two\n", "a")
	require.Equal(t, "one\ntwo\n", got.Text)
}

func TestBlockScalarFoldedIndentedLine(t *testing.T) {
	got := yamlValue(t, "a: >\n  one\n   two\n  three\n", "a")
	require.Equal(t, "one\n two\nthree\n", got.Text)
}

func TestBlockScalarExtraIndentKept(t *testing.T) {
	got := yamlValue(t, "a: |\n  one\n    two\n", "a")
	require.Equal(t, "one\n  two\n", got.Text)
}

func TestBlockScalarEmptyClip(t *testing.T) {
	got := yamlValue(t, "a: |\nb: 1\n", "a")
	require.Equal(t, "", got.Text)
}

func TestBlockScalarEmptyKeepCountsBlankLines(t *testing.T) {
	got := yamlValue(t, "a: |+\n\n\n", "a")
	require.Equal(t, "\n\n", got.Text)
}

func TestBlockScalarEmptyStrip(t *testing.T) {
	got := yamlValue(t, "a: |-\n\n\n", "a")
	require.Equal(t, "", got.Text)
}

func TestBlockScalarStopsAtParentKey(t *testing.T) {
	value, ds := ParseConfigYAML([]byte("a: |\n  text\nb: 2\n"), 0, 16)
	require.Empty(t, ds)
	require.Len(t, value.Entries, 2)
	require.Equal(t, "text\n", value.Entries[0].Value.Text)
	require.Equal(t, "2", value.Entries[1].Value.Text)
}

func TestPlainScalarResolution(t *testing.T) {
	cases := []struct {
		src  string
		kind ValueKind
		text string
	}{
		{"a:\n", ValueNull, ""},
		{"a: null\n", ValueNull, ""},
		{"a: ~\n", ValueNull, ""},
		{"a: true\n", ValueBool, ""},
		{"a: FALSE\n", ValueBool, ""},
		{"a: 42\n", ValueInteger, "42"},
		{"a: -7\n", ValueInteger, "-7"},
		{"a: 1.5\n", ValueDecimal, "1.5"},
		{"a: 1e3\n", ValueString, "1e3"},
		{"a: .inf\n", ValueString, ".inf"},
		{"a: 0x10\n", ValueString, "0x10"},
		{"a: '7'\n", ValueString, "7"},
		{"a: \"8\"\n", ValueString, "8"},
	}
	for _, c := range cases {
		got := yamlValue(t, c.src, "a")
		require.Equal(t, c.kind, got.Kind, "source %q", c.src)
		if c.text != "" {
			require.Equal(t, c.text, got.Text, "source %q", c.src)
		}
	}
}

func TestQuotedScalarEscapes(t *testing.T) {
	got := yamlValue(t, "a: \"x\\ty\\u0041\"\n", "a")
	require.Equal(t, "x\tyA", got.Text)
}

func TestSingleQuotedDoubling(t *testing.T) {
	got := yamlValue(t, "a: 'it''s'\n", "a")
	require.Equal(t, "it's", got.Text)
}

func TestPlainScalarTabIsText(t *testing.T) {
	got := yamlValue(t, "a: x\ty\n", "a")
	require.Equal(t, ValueString, got.Kind)
	require.Equal(t, "x\ty", got.Text)
}

func TestPlainScalarStopsBeforeComment(t *testing.T) {
	got := yamlValue(t, "a: value # comment\n", "a")
	require.Equal(t, "value", got.Text)
}

func TestFlowCollections(t *testing.T) {
	seq := yamlValue(t, "a: [1, 2, 3]\n", "a")
	require.Equal(t, ValueSequence, seq.Kind)
	require.Len(t, seq.Items, 3)
	require.Equal(t, "3", seq.Items[2].Text)

	empty := yamlValue(t, "a: []\n", "a")
	require.Empty(t, empty.Items)

	m := yamlValue(t, "a: {x: 1, y: two}\n", "a")
	require.Equal(t, ValueMapping, m.Kind)
	require.Len(t, m.Entries, 2)
	require.Equal(t, "two", m.Entries[1].Value.Text)

	emptyMap := yamlValue(t, "a: {}\n", "a")
	require.Empty(t, emptyMap.Entries)
}

func TestFlowContinuesOnIndentedLine(t *testing.T) {
	got := yamlValue(t, "a: [\n  1,\n  2]\n", "a")
	require.Len(t, got.Items, 2)
}

func TestFlowTrailingCommaMalformed(t *testing.T) {
	src := []byte("a: [1,]\n")
	_, ds := ParseConfigYAML(src, 0, len(src))
	requireDiags(t, ds, []diagWant{{codeMalformed, msgMalformed, span(6, 7)}})
}

func TestNestedBlockMap(t *testing.T) {
	value, ds := ParseConfigYAML([]byte("a:\n  b:\n    c: 1\n"), 0, 17)
	require.Empty(t, ds)
	require.Len(t, value.Entries, 1)
	inner := value.Entries[0].Value
	require.Equal(t, ValueMapping, inner.Kind)
	require.Len(t, inner.Entries, 1)
	require.Equal(t, "b", inner.Entries[0].Key)
}

func TestKeyWithoutNestedLineIsNull(t *testing.T) {
	value, ds := ParseConfigYAML([]byte("a:\nb: 1\n"), 0, 8)
	require.Empty(t, ds)
	require.Equal(t, ValueNull, value.Entries[0].Value.Kind)
}

func TestJSONDirectiveQuoteRewrite(t *testing.T) {
	src := []byte("{'theme': 'dark'}")
	value, ds := ParseConfigJSON(src, 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, ValueMapping, value.Kind)
	require.Len(t, value.Entries, 1)
	require.Equal(t, "theme", value.Entries[0].Key)
	require.Equal(t, "dark", value.Entries[0].Value.Text)
}

func TestJSONQuoteInsideStringEndsIt(t *testing.T) {
	src := []byte("{'a': 'it's'}")
	_, ds := ParseConfigJSON(src, 0, len(src))
	require.NotEmpty(t, ds)
}

func TestJSONSurrogatePair(t *testing.T) {
	src := []byte("{\"a\": \"\\ud83d\\ude00\"}")
	value, ds := ParseConfigJSON(src, 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, "\U0001F600", value.Entries[0].Value.Text)
}

func TestJSONTypes(t *testing.T) {
	src := []byte("{\"i\": 1, \"d\": 1.5, \"b\": true, \"n\": null, \"s\": \"x\", \"a\": [1], \"o\": {}}")
	value, ds := ParseConfigJSON(src, 0, len(src))
	require.Empty(t, ds)
	kinds := map[string]ValueKind{
		"i": ValueInteger, "d": ValueDecimal, "b": ValueBool, "n": ValueNull,
		"s": ValueString, "a": ValueSequence, "o": ValueMapping,
	}
	for _, entry := range value.Entries {
		require.Equal(t, kinds[entry.Key], entry.Value.Kind, "key %q", entry.Key)
	}
}

func TestJSONKeyMustBeQuoted(t *testing.T) {
	src := []byte("{a: 1}")
	_, ds := ParseConfigJSON(src, 0, len(src))
	require.NotEmpty(t, ds)
}

func TestThousandthsExamples(t *testing.T) {
	cases := []struct {
		text string
		want int32
	}{
		{"0.75", 750},
		{"0.0005", 1},
		{"1", 1000},
		{"-1.5", -1500},
		{"0", 0},
		{"-0", 0},
		{"+2", 2000},
		{"1.2345", 1235},
		{"0.1", 100},
		{"2147483", 2147483000},
	}
	for _, c := range cases {
		got, ok := Thousandths(resolvePlain(c.text, source.Span{}))
		require.True(t, ok, "text %q", c.text)
		require.Equal(t, c.want, got, "text %q", c.text)
	}
}

func TestThousandthsRejectsOtherKinds(t *testing.T) {
	for _, text := range []string{"x", "true"} {
		_, ok := Thousandths(resolvePlain(text, source.Span{}))
		require.False(t, ok, "text %q", text)
	}
}

func TestThousandthsOverflow(t *testing.T) {
	for _, text := range []string{"2147484", "2147483648", "99999999999999999999"} {
		_, ok := Thousandths(resolvePlain(text, source.Span{}))
		require.False(t, ok, "text %q", text)
	}
}

func TestThousandthsRoundingCarry(t *testing.T) {
	got, ok := Thousandths(resolvePlain("0.9999999", source.Span{}))
	require.True(t, ok, "rounding 0.9999999 to thousandths must succeed; got %d", got)
	require.Equal(t, int32(1000), got)
}

func TestFrontmatterConfigExtracted(t *testing.T) {
	src := []byte("---\nconfig:\n  theme: dark\n---\nflowchart LR\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.True(t, p.HasFront, "closed frontmatter must be recognized in %q", src)
	require.Equal(t, span(0, 30), p.Frontmatter)
	require.Equal(t, 30, p.BodyStart)
	require.True(t, p.HasConfig, "frontmatter mapping must expose config; got %+v", p.Config)
	require.Equal(t, "dark", p.Config.Entries[0].Value.Text)
}

func TestFrontmatterScalarRootGivesNoConfig(t *testing.T) {
	src := []byte("---\n5\n---\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.False(t, p.HasConfig, "scalar frontmatter root must not expose config; got %+v", p.Config)
}

func TestFrontmatterEmptyBody(t *testing.T) {
	src := []byte("---\n---\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.True(t, p.HasFront, "empty closed frontmatter must be recognized in %q", src)
	require.False(t, p.HasConfig, "empty frontmatter must not expose config; got %+v", p.Config)
}

func TestFrontmatterNeedsClosingLine(t *testing.T) {
	src := []byte("---\nconfig: 1\n")
	p := Preprocess(src)
	require.False(t, p.HasFront, "unclosed fence must remain diagram text in %q", src)
	require.Zero(t, p.BodyStart)
}

func TestFrontmatterFenceAllowsSpaces(t *testing.T) {
	src := []byte("  ---  \nconfig:\n  theme: dark\n  --- \nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.True(t, p.HasFront, "matching space-indented fences must be recognized in %q", src)
	require.True(t, p.HasConfig, "space-indented frontmatter must expose config; got %+v", p.Config)
}

func TestFrontmatterFenceRequiresIdenticalIndent(t *testing.T) {
	for _, src := range []string{
		"---\ntitle: example\n  ---\nflowchart\n",
		"  ---\ntitle: example\n---\nflowchart\n",
		"\t---\ntitle: example\n        ---\nflowchart\n",
		" \t---\ntitle: example\n\t ---\nflowchart\n",
	} {
		t.Run(src, func(t *testing.T) {
			p := Preprocess([]byte(src))
			require.False(t, p.HasFront, "fences with mismatched indentation must remain diagram text in %q", src)
			require.Zero(t, p.BodyStart)
			require.Empty(t, p.Removed)
		})
	}
}

func TestFrontmatterFenceSkipsMismatchedCloser(t *testing.T) {
	src := []byte("\t--- \r\nvalue: |\r\n  ---\r\n\t--- \r\nflowchart\n")
	p := Preprocess(src)
	require.True(t, p.HasFront, "matching closer after a mismatched fence must close frontmatter in %q", src)
	require.Equal(t, span(0, 31), p.Frontmatter)
	require.Equal(t, 31, p.BodyStart)
	require.Equal(t, []source.Span{span(0, 31)}, p.Removed)
}

func TestDirectiveInitMerged(t *testing.T) {
	src := []byte("%%{init: {\"a\":{\"b\":1},\"x\":1}}%%\n%%{init: {\"a\":{\"c\":2},\"x\":{\"y\":3}}}%%\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.True(t, p.HasInit, "valid init directives must produce merged config; got %+v", p.Init)
	require.Len(t, p.Init.Entries, 2)
	require.Equal(t, "a", p.Init.Entries[0].Key)
	require.Len(t, p.Init.Entries[0].Value.Entries, 2)
	require.Equal(t, "b", p.Init.Entries[0].Value.Entries[0].Key)
	require.Equal(t, "c", p.Init.Entries[0].Value.Entries[1].Key)
	require.Equal(t, ValueMapping, p.Init.Entries[1].Value.Kind)
	require.Len(t, p.Directives, 2)
}

func TestDirectiveInitConfigKeyStaysOrdinary(t *testing.T) {
	src := []byte("%%{init: {\"config\":{\"theme\":\"dark\"}}}%%\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.Len(t, p.Init.Entries, 1)
	require.Equal(t, "config", p.Init.Entries[0].Key)
}

func TestDirectiveUnknownRemovedSilently(t *testing.T) {
	src := []byte("%%{bogus: 1}%%\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.Empty(t, p.Directives)
	require.Equal(t, span(0, 14), p.Removed[0])
}

func TestDirectiveNameContainingInitUnknown(t *testing.T) {
	src := []byte("%%{initialize2: {\"a\":1}}%%\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.False(t, p.HasInit, "initialize2 must not match the init directive name; got %+v", p.Init)
}

func TestDirectiveWrapFlag(t *testing.T) {
	src := []byte("%%{wrap}%%\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.True(t, p.Wrap, "wrap directive must enable preprocessing wrap in %q", src)
	require.Len(t, p.Directives, 1)
	require.True(t, p.Directives[0].Wrap, "parsed wrap directive must retain its wrap flag; got %+v", p.Directives[0])
}

func TestDirectiveInitWithoutColonNoEffect(t *testing.T) {
	src := []byte("%%{init}%%\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.False(t, p.HasInit, "init without a colon must have no config effect; got %+v", p.Init)
	require.Len(t, p.Directives, 1)
}

func TestDirectiveInitOnlyWhitespaceBody(t *testing.T) {
	src := []byte("%%{init: }%%\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.False(t, p.HasInit, "whitespace-only init body must have no config effect; got %+v", p.Init)
}

func TestDirectiveMalformedStillAllowsOthers(t *testing.T) {
	src := []byte("%%{wrap: 1}%%\n%%{init: {\"a\":1}}%%\nflowchart\n")
	p := Preprocess(src)
	require.Len(t, p.Diags, 1)
	require.True(t, p.HasInit, "malformed wrap must not prevent a later valid init; got %+v", p.Init)
}

func TestDirectiveWhitespaceIncludesLineEnds(t *testing.T) {
	for _, text := range []string{
		"%%{init\n: {\"a\":1}}%%\nflowchart\n",
		"%%{init: \n{\"a\":1}}%%\nflowchart\n",
		"%%{\r\ninit\r\n:\r\n{\"a\":1}\r\n}%%\r\nflowchart\r\n",
	} {
		p := Preprocess([]byte(text))
		require.Empty(t, p.Diags, "%q", text)
		require.True(t, p.HasInit, "%q", text)
		require.Len(t, p.Init.Entries, 1, "%q", text)
	}
	p := Preprocess([]byte("%%{ \nwrap\n}%%\nflowchart\n"))
	require.Empty(t, p.Diags)
	require.True(t, p.Wrap)
}

func TestDirectiveUnknownUnclosedRemovedToEnd(t *testing.T) {
	src := []byte("%%{bogus\nflowchart\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.Equal(t, span(0, len(src)), p.Removed[0])
}

func TestDirectiveOnCommentLineStartsDirective(t *testing.T) {
	src := []byte("%% comment %%{wrap}%%\nflowchart\n")
	p := Preprocess(src)
	require.True(t, p.Wrap, "wrap directive inside a comment line must still enable wrap in %q", src)
}

func TestCommentLinesRemoved(t *testing.T) {
	src := []byte("flowchart LR\n%% a comment\n  %% indented\nA --> B\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.Equal(t, []source.Span{span(13, 40)}, p.Removed)
}

func TestCommentLinesMergedWithDirective(t *testing.T) {
	src := []byte("%% comment %%{wrap}%%\nx\n")
	p := Preprocess(src)
	require.True(t, p.Wrap, "merging comment and directive removal must preserve the wrap effect in %q", src)
	require.Equal(t, []source.Span{span(0, 22)}, p.Removed)
}

func TestPreprocessDiagnosticsSorted(t *testing.T) {
	src := []byte("%%{wrap: 1}%%\n%%{init: 5}%%\nflowchart\n")
	p := Preprocess(src)
	require.Len(t, p.Diags, 2)
	require.Equal(t, span(0, 3), p.Diags[0].Span)
	require.Equal(t, span(23, 24), p.Diags[1].Span)
}

func TestPreprocessEmptySource(t *testing.T) {
	p := Preprocess(nil)
	require.Empty(t, p.Diags)
	require.False(t, p.HasFront, "empty source must not contain frontmatter; got span %+v", p.Frontmatter)
	require.False(t, p.HasInit, "empty source must not contain init config; got %+v", p.Init)
	require.Zero(t, p.BodyStart)
}

func TestPreprocessCRLF(t *testing.T) {
	src := []byte("---\r\nconfig:\r\n  theme: dark\r\n---\r\nflowchart\r\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.True(t, p.HasConfig, "CRLF frontmatter must expose config; got %+v", p.Config)
	require.Equal(t, len("---\r\nconfig:\r\n  theme: dark\r\n---\r\n"), p.BodyStart)
}

func TestFrontmatterFailureAtACarriageReturnSpansThatLineBreak(t *testing.T) {
	for _, c := range []struct {
		name string
		src  string
		want source.Span
	}{
		{"lone CR before the closing fence", "---\n0000000000: 0\n0\r---\nflowchart\n", span(19, 20)},
		{"CRLF before the closing fence", "---\n0000000000: 0\n0\r\n---\nflowchart\n", span(19, 21)},
		{"lone CR with text after it", "---\nk: v\n0\rw\n---\nflowchart\n", span(10, 11)},
	} {
		p := Preprocess([]byte(c.src))
		require.Len(t, p.Diags, 1, c.name)
		require.Equal(t, "config/malformed", p.Diags[0].Code, c.name)
		require.Equal(t, c.want, p.Diags[0].Span, c.name)
		require.LessOrEqual(t, p.Diags[0].Span.Start, p.Diags[0].Span.End, c.name)
	}
}

func TestInitDirectiveBodyEndsAtItsClosingFence(t *testing.T) {
	for _, c := range []struct {
		name string
		src  string
		want source.Span
	}{
		{"object missing its closing brace", "%%{init: {'theme':'base'}%%\nflowchart\n", span(24, 24)},
		{"array missing its closing bracket", "%%{init: {'a':[1,2}%%\nflowchart\n", span(18, 18)},
		{"string missing its closing quote", "%%{init: {'a':'b}%%\nflowchart\n", span(16, 16)},
	} {
		p := Preprocess([]byte(c.src))
		require.Len(t, p.Diags, 1, c.name)
		require.Equal(t, "config/malformed", p.Diags[0].Code, c.name)
		require.Equal(t, "malformed config value", p.Diags[0].Message, c.name)
		require.Equal(t, c.want, p.Diags[0].Span, c.name)
		require.False(t, p.HasInit, c.name)
		require.Equal(t, []source.Span{span(0, int(c.want.Start)+3)}, p.Removed[:1], c.name)
	}
}

func xorshift32(state *uint32) uint32 {
	x := *state
	x ^= x << 13
	x ^= x >> 17
	x ^= x << 5
	*state = x
	return x
}

const configAlphabet = " \t\n:-#[]{},'\"|>&*!abc012\\"

func randomConfigText(state *uint32, limit int) []byte {
	n := int(xorshift32(state) % uint32(limit+1))
	out := make([]byte, n)
	for i := range out {
		out[i] = configAlphabet[xorshift32(state)%uint32(len(configAlphabet))]
	}
	return out
}

func requireSpansInside(t *testing.T, ds []diag.Diagnostic, start, end int) {
	t.Helper()
	for _, d := range ds {
		require.GreaterOrEqual(t, d.Span.Start, start, "code %s span %v", d.Code, d.Span)
		require.LessOrEqual(t, d.Span.End, end, "code %s span %v", d.Code, d.Span)
		require.LessOrEqual(t, d.Span.Start, d.Span.End, "code %s span %v", d.Code, d.Span)
	}
}

func TestConfigReaderNoPanicOnRandomBytes(t *testing.T) {
	for i := range 2000 {
		state := uint32(i + 1)
		text := randomConfigText(&state, 64)
		value, ds := ParseConfigYAML(text, 0, len(text))
		requireSpansInside(t, ds, 0, len(text))
		require.NotNil(t, value)
		jsonValue, jsonDs := ParseConfigJSON(text, 0, len(text))
		requireSpansInside(t, jsonDs, 0, len(text))
		require.NotNil(t, jsonValue)
	}
}

func TestConfigReaderRespectsRangeOnRandomBytes(t *testing.T) {
	for i := range 500 {
		state := uint32(i + 1)
		text := randomConfigText(&state, 64)
		start := len(text) / 3
		end := len(text) - len(text)/4
		if start > end {
			start = end
		}
		_, ds := ParseConfigYAML(text, start, end)
		requireSpansInside(t, ds, start, end)
	}
}

func TestThousandthsOnRandomNumbers(t *testing.T) {
	for i := range 2000 {
		state := uint32(i + 1)
		text := randomNumberText(&state)
		value := resolvePlain(text, source.Span{})
		got, ok := Thousandths(value)
		if !ok {
			continue
		}
		require.GreaterOrEqual(t, int64(got), int64(-2147483648))
		require.LessOrEqual(t, int64(got), int64(2147483647))
	}
}

func randomNumberText(state *uint32) string {
	const digits = "0123456789"
	whole := int(xorshift32(state)%6) + 1
	out := make([]byte, 0, 12)
	if xorshift32(state)%2 == 0 {
		out = append(out, '-')
	}
	for range whole {
		out = append(out, digits[xorshift32(state)%10])
	}
	if xorshift32(state)%3 == 0 {
		out = append(out, '.')
		frac := int(xorshift32(state)%4) + 1
		for range frac {
			out = append(out, digits[xorshift32(state)%10])
		}
	}
	return string(out)
}
