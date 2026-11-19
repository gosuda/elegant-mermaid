package syntax

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestConfigQuotedColonLineIsAScalar(t *testing.T) {
	for _, quote := range []string{`"`, `'`} {
		for _, c := range []struct{ name, src, want string }{
			{"next line", "a:\n  Qx: yQ\n", "x: y"},
			{"sequence item", "a:\n  - Qx: yQ\n", "x: y"},
			{"plain continuation", "a: v\n  Qx: yQ\n", "v Qx: yQ"},
		} {
			src := strings.ReplaceAll(c.src, "Q", quote)
			want := strings.ReplaceAll(c.want, "Q", quote)
			value, ds := ParseConfigYAML([]byte(src), 0, len(src))
			require.Empty(t, ds, c.name)
			got := value.Entries[0].Value
			if len(got.Items) > 0 {
				got = got.Items[0]
			}
			require.Equal(t, want, got.Text, c.name)
		}
		root := quote + "a: b" + quote + "\n"
		value, ds := ParseConfigYAML([]byte(root), 0, len(root))
		require.Empty(t, ds)
		require.Equal(t, "a: b", value.Text)
	}
}

func TestFrontmatterUnterminatedQuotedValueFailsAtTheRangeEnd(t *testing.T) {
	for _, quote := range []string{`"`, `'`} {
		src := "---\nconfig:\n  mindmap:\n    " + quote + "colorBy: depth\n---\nflowchart LR\n  A-->B\n"
		rangeEnd := strings.Index(src, "---\nflowchart")
		p := Preprocess([]byte(src))
		require.Len(t, p.Diags, 1, quote)
		require.Equal(t, "config/malformed", p.Diags[0].Code, quote)
		require.Equal(t, "malformed config value", p.Diags[0].Message, quote)
		require.Equal(t, span(rangeEnd, rangeEnd), p.Diags[0].Span, quote)
	}
}
