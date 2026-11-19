package lint

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type scripted func(text string) []diag.Diagnostic

func (s scripted) analyze(src []byte, _ Config) ([]byte, []diag.Diagnostic) {
	ds := s(string(src))
	diag.Sort(ds)
	return src, ds
}

func replace(from, to int, text string) diag.Edit {
	return diag.Edit{Span: source.Span{Start: from, End: to}, NewText: text}
}

func warn(code string, at int, fixes ...diag.Fix) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: diag.SeverityWarning, Span: source.Span{Start: at, End: at + 1}, Fixes: fixes}
}

func fixOf(safety diag.FixSafety, edits ...diag.Edit) diag.Fix {
	return diag.Fix{Title: "fix", Safety: safety, Edits: edits}
}

func erroring(code string, at int) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Span: source.Span{Start: at, End: at + 1}}
}

func TestApplyFixesReachesAFixedPoint(t *testing.T) {
	chain := scripted(func(text string) []diag.Diagnostic {
		switch text {
		case "A":
			return []diag.Diagnostic{warn("t/chain", 0, fixOf(diag.FixSafe, replace(0, 1, "B")))}
		case "B":
			return []diag.Diagnostic{warn("t/chain", 0, fixOf(diag.FixSafe, replace(0, 1, "C")))}
		}
		return nil
	})
	out, applied := applyFixes([]byte("A"), Config{}, diag.FixSafe, chain.analyze)
	require.Equal(t, "C", string(out))
	require.Equal(t, 2, applied)

	out, applied = applyFixes([]byte("C"), Config{}, diag.FixSafe, chain.analyze)
	require.Equal(t, "C", string(out))
	require.Zero(t, applied)
}

func TestApplyFixesStopsAfterTenPasses(t *testing.T) {
	endless := scripted(func(text string) []diag.Diagnostic {
		return []diag.Diagnostic{warn("t/endless", 0, fixOf(diag.FixSafe, replace(len(text), len(text), "x")))}
	})
	out, applied := applyFixes([]byte("seed"), Config{}, diag.FixSafe, endless.analyze)
	require.Equal(t, "seed"+strings.Repeat("x", maxPasses), string(out))
	require.Equal(t, maxPasses, applied)
}

func TestApplyFixesDropsOverlappingFixes(t *testing.T) {
	overlap := scripted(func(text string) []diag.Diagnostic {
		var ds []diag.Diagnostic
		if at := strings.Index(text, "abc"); at >= 0 {
			ds = append(ds, warn("t/a", at, fixOf(diag.FixSafe, replace(at, at+3, "X"))))
		}
		if at := strings.Index(text, "cde"); at >= 0 {
			ds = append(ds, warn("t/b", at, fixOf(diag.FixSafe, replace(at, at+3, "Y"))))
		}
		return ds
	})
	out, applied := applyFixes([]byte("abcdef"), Config{}, diag.FixSafe, overlap.analyze)
	require.Equal(t, "Xdef", string(out))
	require.Equal(t, 1, applied)
}

func TestApplyFixesKeepsDisjointFixes(t *testing.T) {
	disjoint := scripted(func(text string) []diag.Diagnostic {
		var ds []diag.Diagnostic
		for _, w := range []struct{ word, to, code string }{{"ab", "1", "t/a"}, {"cd", "2", "t/b"}} {
			if at := strings.Index(text, w.word); at >= 0 {
				ds = append(ds, warn(w.code, at, fixOf(diag.FixSafe, replace(at, at+2, w.to))))
			}
		}
		return ds
	})
	out, applied := applyFixes([]byte("abXYcd"), Config{}, diag.FixSafe, disjoint.analyze)
	require.Equal(t, "1XY2", string(out))
	require.Equal(t, 2, applied)
}

func TestApplyFixesOrdersInsertionsAtOneOffsetByFixOrder(t *testing.T) {
	inserts := scripted(func(text string) []diag.Diagnostic {
		var ds []diag.Diagnostic
		for _, w := range []struct{ mark, code string }{{"S", "t/a"}, {"T", "t/b"}} {
			if !strings.Contains(text, w.mark) {
				ds = append(ds, warn(w.code, 1, fixOf(diag.FixSafe, replace(1, 1, w.mark))))
			}
		}
		return ds
	})
	out, applied := applyFixes([]byte("ab"), Config{}, diag.FixSafe, inserts.analyze)
	require.Equal(t, "aSTb", string(out))
	require.Equal(t, 2, applied)
}

func TestApplyFixesDropsAWholeMultiEditFix(t *testing.T) {
	multi := scripted(func(text string) []diag.Diagnostic {
		var ds []diag.Diagnostic
		if strings.HasPrefix(text, "a") && len(text) > 4 && text[4] == 'e' {
			ds = append(ds, warn("t/a", 0, fixOf(diag.FixSafe, replace(4, 5, "y"), replace(0, 1, "x"))))
		}
		if at := strings.Index(text, "def"); at >= 0 {
			ds = append(ds, warn("t/b", at, fixOf(diag.FixSafe, replace(at, at+3, "z"))))
		}
		return ds
	})
	out, applied := applyFixes([]byte("abcdef"), Config{}, diag.FixSafe, multi.analyze)
	require.Equal(t, "xbcdyf", string(out))
	require.Equal(t, 1, applied)
}

func TestApplyFixesChoosesBySafety(t *testing.T) {
	both := scripted(func(text string) []diag.Diagnostic {
		if text != "a" {
			return nil
		}
		return []diag.Diagnostic{warn("t/both", 0,
			fixOf(diag.FixUnsafe, replace(0, 1, "U")),
			fixOf(diag.FixSafe, replace(0, 1, "S")),
		)}
	})
	out, applied := applyFixes([]byte("a"), Config{}, diag.FixSafe, both.analyze)
	require.Equal(t, "S", string(out))
	require.Equal(t, 1, applied)
	out, applied = applyFixes([]byte("a"), Config{}, diag.FixUnsafe, both.analyze)
	require.Equal(t, "U", string(out))
	require.Equal(t, 1, applied)

	onlyUnsafe := scripted(func(text string) []diag.Diagnostic {
		if text != "a" {
			return nil
		}
		return []diag.Diagnostic{warn("t/unsafe", 0, fixOf(diag.FixUnsafe, replace(0, 1, "U")))}
	})
	out, applied = applyFixes([]byte("a"), Config{}, diag.FixSafe, onlyUnsafe.analyze)
	require.Equal(t, "a", string(out))
	require.Zero(t, applied)
}

func TestApplyFixesDiscardsAPassThatAddsAnError(t *testing.T) {
	introduces := scripted(func(text string) []diag.Diagnostic {
		switch text {
		case "ok":
			return []diag.Diagnostic{warn("t/fixme", 0, fixOf(diag.FixSafe, replace(0, 2, "bad")))}
		case "bad":
			return []diag.Diagnostic{erroring("t/bad", 0)}
		}
		return nil
	})
	out, applied := applyFixes([]byte("ok"), Config{}, diag.FixSafe, introduces.analyze)
	require.Equal(t, "ok", string(out))
	require.Zero(t, applied)

	later := scripted(func(text string) []diag.Diagnostic {
		switch text {
		case "a":
			return []diag.Diagnostic{warn("t/step", 0, fixOf(diag.FixSafe, replace(0, 1, "b")))}
		case "b":
			return []diag.Diagnostic{warn("t/step", 0, fixOf(diag.FixSafe, replace(0, 1, "bad")))}
		case "bad":
			return []diag.Diagnostic{erroring("t/bad", 0)}
		}
		return nil
	})
	out, applied = applyFixes([]byte("a"), Config{}, diag.FixSafe, later.analyze)
	require.Equal(t, "b", string(out))
	require.Equal(t, 1, applied)
}

func TestApplyFixesAcceptsAPassThatKeepsItsErrors(t *testing.T) {
	keeps := scripted(func(text string) []diag.Diagnostic {
		ds := []diag.Diagnostic{erroring("t/pre", 0)}
		if text == "!ok" {
			ds = append(ds, warn("t/fix", 1, fixOf(diag.FixSafe, replace(1, 3, "fine"))))
		}
		return ds
	})
	out, applied := applyFixes([]byte("!ok"), Config{}, diag.FixSafe, keeps.analyze)
	require.Equal(t, "!fine", string(out))
	require.Equal(t, 1, applied)
}

func TestApplyFixesCountsErrorMultiplicity(t *testing.T) {
	doubles := scripted(func(text string) []diag.Diagnostic {
		switch text {
		case "a":
			return []diag.Diagnostic{erroring("t/pre", 0), warn("t/fix", 0, fixOf(diag.FixSafe, replace(0, 1, "bb")))}
		case "bb":
			return []diag.Diagnostic{erroring("t/pre", 0), erroring("t/pre", 0)}
		}
		return nil
	})
	out, applied := applyFixes([]byte("a"), Config{}, diag.FixSafe, doubles.analyze)
	require.Equal(t, "a", string(out))
	require.Zero(t, applied)
}

func TestApplyFixesIgnoresInvalidAndEmptyFixes(t *testing.T) {
	invalid := scripted(func(text string) []diag.Diagnostic {
		return []diag.Diagnostic{
			warn("t/beyond", 0, fixOf(diag.FixSafe, replace(5, 9, "x"))),
			warn("t/inverted", 0, fixOf(diag.FixSafe, replace(2, 1, "x"))),
			warn("t/negative", 0, fixOf(diag.FixSafe, replace(-1, 0, "x"))),
			warn("t/empty", 0, diag.Fix{Title: "nothing", Safety: diag.FixSafe}),
			warn("t/self-overlap", 0, fixOf(diag.FixSafe, replace(0, 2, "x"), replace(1, 2, "y"))),
		}
	})
	out, applied := applyFixes([]byte("abc"), Config{}, diag.FixSafe, invalid.analyze)
	require.Equal(t, "abc", string(out))
	require.Zero(t, applied)
}

func TestApplyFixesStopsOnANoOpEdit(t *testing.T) {
	noop := scripted(func(text string) []diag.Diagnostic {
		return []diag.Diagnostic{warn("t/noop", 0, fixOf(diag.FixSafe, replace(0, 1, "a")))}
	})
	out, applied := applyFixes([]byte("a"), Config{}, diag.FixSafe, noop.analyze)
	require.Equal(t, "a", string(out))
	require.Zero(t, applied)
}

func TestApplyFixesNeverAliasesTheInput(t *testing.T) {
	quiet := scripted(func(string) []diag.Diagnostic { return nil })
	src := []byte("abc")
	out, applied := applyFixes(src, Config{}, diag.FixSafe, quiet.analyze)
	require.Zero(t, applied)
	out[0] = 'X'
	require.Equal(t, "abc", string(src))
}

func TestApplyFixesSkipsSuppressedDiagnostics(t *testing.T) {
	analyze := func(src []byte, cfg Config) ([]byte, []diag.Diagnostic) {
		var syntax []diag.Diagnostic
		if at := strings.Index(string(src), "bad"); at >= 0 {
			d := warn("config/unknown-key", at, fixOf(diag.FixUnsafe, replace(at, at+3, "good")))
			d.Span.End = at + 3
			syntax = append(syntax, d)
		}
		a := &Analysis{Source: src, Block: Block{Source: src}, Syntax: syntax}
		return src, Run(a, cfg).All()
	}
	plain := "head\nbad\n"
	out, applied := applyFixes([]byte(plain), Config{}, diag.FixUnsafe, analyze)
	require.Equal(t, "head\ngood\n", string(out))
	require.Equal(t, 1, applied)

	suppressed := "head\n%% emd-disable-next-line config/unknown-key: legacy\nbad\n"
	out, applied = applyFixes([]byte(suppressed), Config{}, diag.FixUnsafe, analyze)
	require.Equal(t, suppressed, string(out))
	require.Zero(t, applied)
}

func TestApplyFixesOnRealDiagrams(t *testing.T) {
	out, applied := ApplyFixes([]byte("flowchart LR\n  A -> B\n"), Config{}, diag.FixSafe)
	require.Equal(t, "flowchart LR\n  A --> B\n", string(out))
	require.Equal(t, 1, applied)

	clean := "flowchart LR\n  A --> B\n"
	out, applied = ApplyFixes([]byte(clean), Config{}, diag.FixUnsafe)
	require.Equal(t, clean, string(out))
	require.Zero(t, applied)

	unsafe := "flowchart TD\n  A --> B\n  end\n"
	out, applied = ApplyFixes([]byte(unsafe), Config{}, diag.FixSafe)
	require.Equal(t, unsafe, string(out))
	require.Zero(t, applied)
	out, applied = ApplyFixes([]byte(unsafe), Config{}, diag.FixUnsafe)
	require.Equal(t, "flowchart TD\n  A --> B\n", string(out))
	require.Equal(t, 1, applied)
}

func TestApplyFixesRepairsInvalidUTF8(t *testing.T) {
	src := []byte("flowchart LR\n  A -> B\xff\n")
	out, _ := ApplyFixes(src, Config{}, diag.FixSafe)
	require.True(t, strings.Contains(string(out), "\uFFFD"))
	require.NotContains(t, string(out), "\xff")
	require.Equal(t, byte(0xff), src[len(src)-2])
}

func TestApplyFixesTreatsAMovedErrorAsTheSameError(t *testing.T) {
	src := "flowchart LR\n  A -> B\n  C[unclosed\n"
	out, applied := ApplyFixes([]byte(src), Config{}, diag.FixSafe)
	require.Equal(t, "flowchart LR\n  A --> B\n  C[unclosed\n", string(out))
	require.Equal(t, 1, applied)
}

func TestApplyFixesShiftsErrorOffsetsThroughEdits(t *testing.T) {
	grows := scripted(func(text string) []diag.Diagnostic {
		ds := []diag.Diagnostic{erroring("t/later", strings.Index(text, "!"))}
		if strings.HasPrefix(text, "a") {
			ds = append(ds, warn("t/grow", 0, fixOf(diag.FixSafe, replace(0, 1, "bbb"))))
		}
		return ds
	})
	out, applied := applyFixes([]byte("a-!"), Config{}, diag.FixSafe, grows.analyze)
	require.Equal(t, "bbb-!", string(out))
	require.Equal(t, 1, applied)
}

func TestShiftOffset(t *testing.T) {
	edits := []edit{{start: 2, end: 4, text: "xyz"}, {start: 6, end: 6, text: "ins"}, {start: 8, end: 10, text: ""}}
	cases := []struct{ offset, want int }{
		{0, 0}, {1, 1}, {2, 2}, {3, 2}, {4, 5}, {5, 6}, {6, 10}, {7, 11}, {8, 12}, {9, 12}, {10, 12}, {12, 14},
	}
	for _, c := range cases {
		require.Equal(t, c.want, shiftOffset(edits, c.offset), c.offset)
	}
}
