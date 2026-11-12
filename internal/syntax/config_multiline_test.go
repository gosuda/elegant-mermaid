package syntax

import (
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
	for _, src := range []string{"a:\n  - item\n", "a:\n  first\n\tsecond\n", "a:\n  first\n  invalid: mapping\n"} {
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
