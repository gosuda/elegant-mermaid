package lint

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func TestApplyHostFixesRemovesWholeLines(t *testing.T) {
	cases := []struct{ name, host, want string }{
		{
			name: "last line of a top-level fence",
			host: "# T\n\n```mermaid\nflowchart TD\n  A --> B\n  end\n```\n\nafter\n",
			want: "# T\n\n```mermaid\nflowchart TD\n  A --> B\n```\n\nafter\n",
		},
		{
			name: "last line inside a block quote",
			host: "> ```mermaid\n> flowchart TD\n>   A --> B\n>   end\n> ```\n",
			want: "> ```mermaid\n> flowchart TD\n>   A --> B\n> ```\n",
		},
		{
			name: "last line inside a list item",
			host: "- item\n\n  ```mermaid\n  flowchart TD\n    A --> B\n    end\n  ```\n",
			want: "- item\n\n  ```mermaid\n  flowchart TD\n    A --> B\n  ```\n",
		},
		{
			name: "last line with CRLF endings",
			host: "```mermaid\r\nflowchart TD\r\n  A --> B\r\n  end\r\n```\r\n",
			want: "```mermaid\r\nflowchart TD\r\n  A --> B\r\n```\r\n",
		},
		{
			name: "last line of an unclosed fence",
			host: "```mermaid\nflowchart TD\n  A --> B\n  end\n",
			want: "```mermaid\nflowchart TD\n  A --> B\n",
		},
		{
			name: "middle line of a top-level fence",
			host: "```mermaid\nflowchart TD\n  end\n  A --> B\n```\n",
			want: "```mermaid\nflowchart TD\n  A --> B\n```\n",
		},
		{
			name: "middle line inside a block quote",
			host: "> ```mermaid\n> flowchart TD\n>   end\n>   A --> B\n> ```\n",
			want: "> ```mermaid\n> flowchart TD\n>   A --> B\n> ```\n",
		},
		{
			name: "first and last lines in one pass",
			host: "```mermaid\nflowchart TD\n  end\n  A --> B\n  end\n```\n",
			want: "```mermaid\nflowchart TD\n  A --> B\n```\n",
		},
		{
			name: "a blank line before the closing fence stays",
			host: "```mermaid\nflowchart TD\n  A --> B\n  end\n\n```\n",
			want: "```mermaid\nflowchart TD\n  A --> B\n\n```\n",
		},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			out, applied := ApplyHostFixes([]byte(c.host), Config{}, diag.FixUnsafe)
			require.Equal(t, c.want, string(out))
			require.Positive(t, applied)
			again, more := ApplyHostFixes(out, Config{}, diag.FixUnsafe)
			require.Equal(t, c.want, string(again))
			require.Zero(t, more)
		})
	}
}

func TestHostFixEditsStayOnHostLines(t *testing.T) {
	host := []byte("> ```mermaid\n> flowchart TD\n>   A --> B\n>   end\n> ```\n")
	var edits []diag.Edit
	for _, d := range LintHost(host, Config{}).Diagnostics {
		for _, f := range d.Fixes {
			edits = append(edits, f.Edits...)
		}
	}
	require.Len(t, edits, 1)
	start, end := edits[0].Span.Start, edits[0].Span.End
	require.Equal(t, ">   end\n", string(host[start:end]))
	require.Empty(t, edits[0].NewText)
}

func TestApplyHostFixesKeepsInLineEditsInTheirBlock(t *testing.T) {
	host := "> ```mermaid\n> flowchart LR\n>   A -> B\n> ```\n"
	out, applied := ApplyHostFixes([]byte(host), Config{}, diag.FixSafe)
	require.Equal(t, "> ```mermaid\n> flowchart LR\n>   A --> B\n> ```\n", string(out))
	require.Equal(t, 1, applied)
}
