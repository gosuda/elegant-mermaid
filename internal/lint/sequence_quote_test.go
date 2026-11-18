package lint

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const quoteUnclosedCode = "sequence/quote-unclosed"

func TestQuoteUnclosedIsAnUnsafeWarningWithAFix(t *testing.T) {
	src := "sequenceDiagram\n  participant \"Bob\n  A->>Bob: hi\n"
	res := lintResult(src, Config{})
	require.Empty(t, res.Lint)
	found := withCode(res.Syntax, quoteUnclosedCode)
	require.Len(t, found, 1)
	end := len("sequenceDiagram\n  participant \"Bob")
	require.Equal(t, diag.SeverityWarning, found[0].Severity)
	require.Equal(t, source.Span{Start: end - len("\"Bob"), End: end}, found[0].Span)
	require.Equal(t, []diag.Fix{{
		Title:  "Insert the closing quote",
		Safety: diag.FixUnsafe,
		Edits:  []diag.Edit{{Span: source.Span{Start: end, End: end}, NewText: "\""}},
	}}, found[0].Fixes)

	kept, applied := ApplyFixes([]byte(src), Config{}, diag.FixSafe)
	require.Zero(t, applied)
	require.Equal(t, src, string(kept))

	fixed, applied := ApplyFixes([]byte(src), Config{}, diag.FixUnsafe)
	require.Equal(t, 1, applied)
	require.Equal(t, "sequenceDiagram\n  participant \"Bob\"\n  A->>Bob: hi\n", string(fixed))
}

func TestQuoteUnclosedSuppression(t *testing.T) {
	src := "sequenceDiagram\n  %% emd-disable-next-line sequence/quote-unclosed: quoted\n  participant \"Bob\n"
	res := lintResult(src, Config{})
	require.Empty(t, res.Syntax)
	require.Empty(t, res.Lint)
	kept, applied := ApplyFixes([]byte(src), Config{}, diag.FixUnsafe)
	require.Zero(t, applied)
	require.Equal(t, src, string(kept))
}
