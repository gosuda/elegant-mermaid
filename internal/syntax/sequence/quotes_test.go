package sequence

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func quoteWarnings(src string) []diag.Diagnostic {
	_, ds := parse(src)
	var out []diag.Diagnostic
	for _, d := range ds {
		if d.Code == codeQuoteUnclosed {
			out = append(out, d)
		}
	}
	return out
}

func TestUnclosedQuoteWarnsOnNamesAndAliases(t *testing.T) {
	cases := []struct {
		name string
		src  string
		hits []string
	}{
		{"participant name", "sequenceDiagram\n  participant \"Bob\n  A->>Bob: hi\n", []string{"\"Bob"}},
		{"actor name", "sequenceDiagram\n  actor \"Bob\n", []string{"\"Bob"}},
		{"alias", "sequenceDiagram\n  participant Alice as \"Alias\n", []string{"\"Alias"}},
		{"name and alias", "sequenceDiagram\n  participant \"Bob as \"B\n", []string{"\"Bob", "\"B"}},
		{"created participant", "sequenceDiagram\n  create participant \"Bob\n", []string{"\"Bob"}},
		{"inside a box", "sequenceDiagram\n  box Group\n    participant \"Bob\n  end\n", []string{"\"Bob"}},
		{"inside a block", "sequenceDiagram\n  alt ok\n    participant \"Bob\n  end\n", []string{"\"Bob"}},
		{"closed name", "sequenceDiagram\n  participant \"Bob\"\n", nil},
		{"closed alias", "sequenceDiagram\n  participant Alice as \"Alias\"\n", nil},
		{"closed quote with a tail", "sequenceDiagram\n  participant \"Bob\" x\n", nil},
		{"plain name", "sequenceDiagram\n  participant Bob\n", nil},
		{"quote not at the start", "sequenceDiagram\n  participant Bo\"b\n", nil},
		{"destroy is not a declaration", "sequenceDiagram\n  destroy \"Bob\n", nil},
		{"message actor is not a declaration", "sequenceDiagram\n  A->>\"Bob: hi\n", nil},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			var got []string
			for _, d := range quoteWarnings(c.src) {
				require.Equal(t, diag.SeverityWarning, d.Severity)
				got = append(got, c.src[d.Span.Start:d.Span.End])
			}
			require.Equal(t, c.hits, got)
		})
	}
}

func TestUnclosedQuoteWarningCarriesTheRegistryRowAndAnUnsafeFix(t *testing.T) {
	src := "sequenceDiagram\n  participant \"Bob \t\n"
	found := quoteWarnings(src)
	require.Len(t, found, 1)
	row := lintRow(codeQuoteUnclosed)
	require.NotEmpty(t, row.Summary)
	require.Equal(t, row.Summary, found[0].Message)
	require.Equal(t, row.Help, found[0].Help)
	end := len("sequenceDiagram\n  participant \"Bob")
	require.Equal(t, source.Span{Start: end - len("\"Bob"), End: end}, found[0].Span)
	require.Equal(t, []diag.Fix{{
		Title:  "Insert the closing quote",
		Safety: diag.FixUnsafe,
		Edits:  []diag.Edit{{Span: source.Span{Start: end, End: end}, NewText: "\""}},
	}}, found[0].Fixes)
}

func TestUnclosedQuoteIsNotASyntaxError(t *testing.T) {
	_, ds := parse("sequenceDiagram\n  participant \"Bob\n  A->>Bob: hi\n")
	for _, d := range ds {
		require.NotEqual(t, diag.SeverityError, d.Severity, d.Code)
	}
}
