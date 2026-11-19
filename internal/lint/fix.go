package lint

import (
	"bytes"
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

const maxPasses = 10

type analyzeFunc func(src []byte, cfg Config) ([]byte, []diag.Diagnostic)

func ApplyFixes(src []byte, cfg Config, limit diag.FixSafety) ([]byte, int) {
	return applyFixes(src, cfg, limit, analyzeSource)
}

func analyzeSource(src []byte, cfg Config) ([]byte, []diag.Diagnostic) {
	a := Analyze(src)
	return a.Source, Run(a, cfg).All()
}

func applyFixes(src []byte, cfg Config, limit diag.FixSafety, analyze analyzeFunc) ([]byte, int) {
	text, ds := analyze(src, cfg)
	text = slices.Clone(text)
	applied := 0
	for range maxPasses {
		kept := dropOverlaps(chooseFixes(ds, limit, len(text)))
		if len(kept) == 0 {
			break
		}
		edits := sortedEdits(kept)
		next := splice(text, edits)
		if bytes.Equal(next, text) {
			break
		}
		nextText, nextDs := analyze(next, cfg)
		if introducesError(ds, nextDs, edits) {
			break
		}
		text, ds, applied = slices.Clone(nextText), nextDs, applied+len(kept)
	}
	return text, applied
}

type edit struct {
	start int
	end   int
	text  string
	seq   int
}

type chosenFix struct {
	edits []edit
}

func compareEdits(a, b edit) int {
	return cmp.Or(cmp.Compare(a.start, b.start), cmp.Compare(a.end, b.end), cmp.Compare(a.seq, b.seq))
}

func chooseFixes(ds []diag.Diagnostic, limit diag.FixSafety, size int) []chosenFix {
	var chosen []chosenFix
	for i := range ds {
		fix, ok := firstWithin(ds[i].Fixes, limit)
		if !ok {
			continue
		}
		if edits, valid := fixEdits(fix, len(chosen), size); valid {
			chosen = append(chosen, chosenFix{edits: edits})
		}
	}
	return chosen
}

func firstWithin(fixes []diag.Fix, limit diag.FixSafety) (diag.Fix, bool) {
	for _, f := range fixes {
		if f.Safety <= limit {
			return f, true
		}
	}
	return diag.Fix{}, false
}

func fixEdits(fix diag.Fix, seq, size int) ([]edit, bool) {
	if len(fix.Edits) == 0 {
		return nil, false
	}
	edits := make([]edit, len(fix.Edits))
	for i, e := range fix.Edits {
		if e.Span.Start < 0 || e.Span.Start > e.Span.End || e.Span.End > size {
			return nil, false
		}
		edits[i] = edit{start: e.Span.Start, end: e.Span.End, text: e.NewText, seq: seq}
	}
	slices.SortStableFunc(edits, compareEdits)
	return edits, !selfOverlapping(edits)
}

func selfOverlapping(edits []edit) bool {
	for i := 1; i < len(edits); i++ {
		if conflicts(edits[i-1], edits[i]) {
			return true
		}
	}
	return false
}

func conflicts(a, b edit) bool {
	if compareEdits(a, b) > 0 {
		a, b = b, a
	}
	return b.start < a.end
}

func dropOverlaps(fixes []chosenFix) []chosenFix {
	ordered := slices.Clone(fixes)
	slices.SortStableFunc(ordered, func(a, b chosenFix) int {
		return compareEdits(a.edits[0], b.edits[0])
	})
	var kept []chosenFix
	for _, f := range ordered {
		if !clashes(kept, f) {
			kept = append(kept, f)
		}
	}
	return kept
}

func clashes(kept []chosenFix, f chosenFix) bool {
	for _, k := range kept {
		for _, a := range k.edits {
			if slices.ContainsFunc(f.edits, func(b edit) bool { return conflicts(a, b) }) {
				return true
			}
		}
	}
	return false
}

func sortedEdits(fixes []chosenFix) []edit {
	var all []edit
	for _, f := range fixes {
		all = append(all, f.edits...)
	}
	slices.SortStableFunc(all, compareEdits)
	return all
}

func splice(text []byte, edits []edit) []byte {
	out := make([]byte, 0, len(text))
	pos := 0
	for _, e := range edits {
		out = append(out, text[pos:e.start]...)
		out = append(out, e.text...)
		pos = e.end
	}
	return append(out, text[pos:]...)
}

func shiftOffset(edits []edit, offset int) int {
	delta := 0
	for _, e := range edits {
		switch {
		case e.end <= offset:
			delta += len(e.text) - (e.end - e.start)
		case e.start <= offset:
			return e.start + delta
		default:
			return offset + delta
		}
	}
	return offset + delta
}

type errorKey struct {
	code  string
	start int
}

func errorCounts(ds []diag.Diagnostic, at func(int) int) map[errorKey]int {
	counts := map[errorKey]int{}
	for i := range ds {
		if ds[i].Severity == diag.SeverityError {
			counts[errorKey{code: ds[i].Code, start: at(ds[i].Span.Start)}]++
		}
	}
	return counts
}

func introducesError(before, after []diag.Diagnostic, applied []edit) bool {
	was := errorCounts(before, func(offset int) int { return shiftOffset(applied, offset) })
	for key, n := range errorCounts(after, func(offset int) int { return offset }) {
		if n > was[key] {
			return true
		}
	}
	return false
}
