package lint

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func TestLabelAtInUnquoted(t *testing.T) {
	const code = "flowchart/label-at-in-unquoted"
	cases := []struct {
		name string
		node string
		want bool
	}{
		{"square", "A[user@host]", true},
		{"stadium", "A([user@host])", true},
		{"subroutine", "A[[user@host]]", true},
		{"cylinder", "A[(user@host)]", true},
		{"quoted", "A[\"user@host\"]", false},
		{"markdown", "A[\"`user@host`\"]", false},
		{"round", "A(user@host)", false},
		{"trapezoid", "A[/user@host\\]", false},
		{"lean right", "A[/user@host/]", false},
		{"slash pair with spaces", "A[ /user@host/ ]", false},
		{"no at sign", "A[user host]", false},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			src := "flowchart TD\n" + tc.node + "\n"
			res := lintResult(src, Config{})
			require.Empty(t, res.Syntax)
			found := withCode(res.Lint, code)
			if !tc.want {
				require.Empty(t, found)
				return
			}
			at := strings.IndexByte(src, '@')
			require.Len(t, found, 1)
			require.Equal(t, diag.SeverityWarning, found[0].Severity)
			require.Equal(t, at, found[0].Span.Start)
			require.Equal(t, at+1, found[0].Span.End)
		})
	}
}

func TestLabelAtInUnquotedDeclarationOrder(t *testing.T) {
	const code = "flowchart/label-at-in-unquoted"
	src := "flowchart TD\nA[first@host@other]\nsubgraph outer\nsubgraph inner\nB([nested@host])\nend\nend\nA[last@host]\n"
	res := lintResult(src, Config{})
	require.Empty(t, res.Syntax)
	found := withCode(res.Lint, code)
	require.Len(t, found, 3)
	for i, label := range []string{"first@host", "nested@host", "last@host"} {
		at := strings.Index(src, label) + strings.IndexByte(label, '@')
		require.Equal(t, at, found[i].Span.Start)
		require.Equal(t, at+1, found[i].Span.End)
	}
}

func TestSubgraphIDCollision(t *testing.T) {
	const code = "flowchart/subgraph-id-collision"
	cases := []struct {
		name string
		src  string
		hits []string
	}{
		{"member repeats its own subgraph id", "flowchart TD\nsubgraph S1[\"Container\"]\n  B --> S1[\"Problem\"]\nend\n", []string{"S1"}},
		{"bare reference inside", "flowchart TD\nsubgraph S1\n  S1\nend\n", []string{"S1"}},
		{"nested member repeats the outer id", "flowchart TD\nsubgraph outer\n  subgraph inner\n    outer --> x\n  end\nend\n", []string{"outer"}},
		{"reference after the end keyword", "flowchart TD\nsubgraph S1\n  A\nend\nB --> S1\n", nil},
		{"different ids", "flowchart TD\nsubgraph S1\n  A --> B\nend\n", nil},
		{"sibling subgraph id", "flowchart TD\nsubgraph S1\n  A\nend\nsubgraph S2\n  S1\nend\n", nil},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			res := lintResult(tc.src, Config{})
			require.Empty(t, res.Syntax)
			var got []string
			for _, d := range withCode(res.Lint, code) {
				require.Equal(t, diag.SeverityWarning, d.Severity)
				got = append(got, tc.src[d.Span.Start:d.Span.End])
			}
			require.Equal(t, tc.hits, got)
		})
	}
}
