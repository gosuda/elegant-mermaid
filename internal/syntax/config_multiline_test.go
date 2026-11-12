package syntax

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestConfigMultilinePlain(t *testing.T) {
	cases := []struct {
		src, want  string
		start, end int
	}{
		{"description:\n  first line,\n  `second` line.\nconfig:\n  layout: \"dagre\"\n", "first line, `second` line.", 15, 43},
		{"a: first\n  second\nb: end\n", "first second", 3, 17},
		{"a: first\n\n  second\n", "first\nsecond", 3, 18},
		{"a:\r\n  first\r\n  second\r\n", "first second", 6, 21},
	}
	for _, c := range cases {
		t.Run(c.want, func(t *testing.T) {
			v, ds := ParseConfigYAML([]byte(c.src), 0, len(c.src))
			require.Empty(t, ds)
			require.Equal(t, c.want, v.Entries[0].Value.Text)
			require.Equal(t, span(c.start, c.end), v.Entries[0].Value.Span)
		})
	}
}

func TestConfigDescriptionFrontmatter(t *testing.T) {
	src := []byte("---\ndescription:\n  Renders a basic top-down flowchart under dagre layout, covering rectangle,\n  round, and decision node shapes plus labeled edges and a FontAwesome icon\n  label, as a baseline smoke test.\nconfig:\n  layout: \"dagre\"\n---\nflowchart TD\n")
	p := Preprocess(src)
	require.Empty(t, p.Diags)
	require.Equal(t, "Renders a basic top-down flowchart under dagre layout, covering rectangle, round, and decision node shapes plus labeled edges and a FontAwesome icon label, as a baseline smoke test.", p.Root.Entries[0].Value.Text)
	require.Equal(t, "dagre", p.Config.Entries[0].Value.Text)
}

func TestConfigNestedScalarRejections(t *testing.T) {
	for _, src := range []string{"a:\n  first\n\tsecond\n", "a:\n  first\n  invalid: mapping\n"} {
		_, ds := ParseConfigYAML([]byte(src), 0, len(src))
		require.NotEmpty(t, ds)
		require.Equal(t, "config/malformed", ds[0].Code)
	}
	for _, src := range []string{"a:\n  &anchor\n", "a:\n  *alias\n"} {
		_, ds := ParseConfigYAML([]byte(src), 0, len(src))
		require.NotEmpty(t, ds)
		require.Equal(t, "config/unsupported-anchor", ds[0].Code)
	}
}

func TestConfigBlockSequences(t *testing.T) {
	src := []byte("items:\n  - alpha\n  - 12\n  - true\nother: end\n")
	v, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	items := v.Entries[0].Value.Items
	require.Len(t, items, 3)
	require.Equal(t, "alpha", items[0].Text)
	require.Equal(t, span(11, 16), items[0].Span)
	require.Equal(t, ValueInteger, items[1].Kind)
	require.Equal(t, "12", items[1].Text)
	require.Equal(t, true, items[2].Bool)
	require.Equal(t, "end", v.Entries[1].Value.Text)
}

func TestConfigSequenceMapsAndNesting(t *testing.T) {
	src := []byte("items:\n  - name: alpha\n    values:\n      - first\n      - second\n  - name: beta\n    enabled: true\n")
	v, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	items := v.Entries[0].Value.Items
	require.Len(t, items, 2)
	require.Equal(t, "alpha", items[0].Entries[0].Value.Text)
	require.Equal(t, span(11, 15), items[0].Entries[0].KeySpan)
	require.Equal(t, "first", items[0].Entries[1].Value.Items[0].Text)
	require.Equal(t, "second", items[0].Entries[1].Value.Items[1].Text)
	require.Equal(t, "beta", items[1].Entries[0].Value.Text)
	require.True(t, items[1].Entries[1].Value.Bool)
}

func TestConfigMultilineQuoted(t *testing.T) {
	for _, c := range []struct{ src, want string }{
		{"a: \"first  \n  second\"\n", "first second"},
		{"a: 'first\\n  second'\n", "first\\n  second"},
		{"a: 'first  \n \n  second'\n", "first\nsecond"},
		{"a: \"first\\\n  second\"\n", "firstsecond"},
		{"a: \"first\\\n\n  second\"\n", "firstsecond"},
		{"a: \"first\\n\n  second\"\n", "first\n second"},
		{"a: \"first\r\n  second\"\n", "first second"},
	} {
		v, ds := ParseConfigYAML([]byte(c.src), 0, len(c.src))
		require.Empty(t, ds)
		require.Equal(t, c.want, v.Entries[0].Value.Text)
		require.Equal(t, span(3, len(c.src)-1), v.Entries[0].Value.Span)
	}
}

func TestConfigSequenceIndentless(t *testing.T) {
	src := []byte("items:\n- alpha\n- beta\nother: end\n")
	v, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	require.Equal(t, "beta", v.Entries[0].Value.Items[1].Text)
	require.Equal(t, "end", v.Entries[1].Value.Text)
}

func TestConfigNewYAMLFormsRejectMalformed(t *testing.T) {
	for _, src := range []string{
		"a:\n  - name: alpha\n   enabled: true\n",
		"a:\n\t- item\n",
		"a: \"first\n  second\n",
		"a: 'first\n  second\n",
		"a: \"first\n---\nsecond\"\n",
		"a: 'first\n...\nsecond'\n",
		"a: \"first\\q\n  second\"\n",
	} {
		_, ds := ParseConfigYAML([]byte(src), 0, len(src))
		require.NotEmpty(t, ds, src)
		require.Equal(t, "config/malformed", ds[0].Code)
	}
	src := []byte("{\"a\":\"first\n  second\"}")
	_, ds := ParseConfigJSON(src, 0, len(src))
	require.NotEmpty(t, ds)
	require.Equal(t, "config/malformed", ds[0].Code)
}

func TestConfigSequenceDepth(t *testing.T) {
	for _, levels := range []int{63, 64} {
		var src strings.Builder
		src.WriteString("a:\n")
		for depth := 1; depth <= levels; depth++ {
			src.WriteString(strings.Repeat("  ", depth) + "-\n")
		}
		text := src.String()
		_, ds := ParseConfigYAML([]byte(text), 0, len(text))
		if levels == 63 {
			require.Empty(t, ds)
			continue
		}
		requireDiags(t, ds, []diagWant{{"limit/nesting-depth", msgDepth, span(strings.LastIndex(text, "-"), strings.LastIndex(text, "-")+1)}})
	}
}

func TestConfigSequenceQuotedAndFlowScalars(t *testing.T) {
	src := []byte("items:\n  - \"a: b\"\n  - 'c: d'\n  - [first, second]\n")
	v, ds := ParseConfigYAML(src, 0, len(src))
	require.Empty(t, ds)
	items := v.Entries[0].Value.Items
	require.Equal(t, "a: b", items[0].Text)
	require.Equal(t, "c: d", items[1].Text)
	require.Equal(t, "first", items[2].Items[0].Text)
	require.Equal(t, "second", items[2].Items[1].Text)
}
