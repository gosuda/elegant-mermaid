package math_test

import (
	"errors"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	emmath "github.com/gosuda/elegant-mermaid/internal/math"
)

func checkDiagnosticSpans(t *testing.T, formula string, diagnostics []diag.Diagnostic) {
	t.Helper()
	for _, d := range diagnostics {
		if d.Span.Start < 0 || d.Span.Start > d.Span.End || d.Span.End > len(formula) {
			t.Fatalf("diagnostic span %+v outside %d bytes", d.Span, len(formula))
		}
	}
}

func checkBoxExtent(t *testing.T, box emmath.Box) {
	t.Helper()
	if box.W < 0 || box.A < 0 || box.D < 0 {
		t.Fatalf("negative extent %+v", box)
	}
	for _, leaf := range box.Leaves {
		inside, err := geom.Contains(box.Bounds(), leaf.Rect)
		if err != nil || !inside {
			t.Fatalf("leaf %+v outside %+v (err %v)", leaf.Rect, box.Bounds(), err)
		}
	}
}

func FuzzMath(f *testing.F) {
	for _, seed := range []string{
		"", "x", "x(t)", `\frac{a}{b}`, `\sqrt[3]{x}`, `\sum_{k=1}^{n}k`, `\int^{b}_{a}`, `\lim_{x\to 0}`,
		`\left(x\right)`, `\left\{\frac{1}{2}\right.`, `\mathbf{x}\text{a b}`, `\alpha\Omega`, `x^{`, `\foo`,
		`{{{{x}}}}`, `x^1^2`, `\right)`, "\\", "\xff\\\xc3", `\text{\$}`, `a\,b\;c\quad d`,
	} {
		f.Add(seed)
	}
	f.Fuzz(func(t *testing.T, formula string) {
		parsed := emmath.Parse(formula)
		checkDiagnosticSpans(t, formula, parsed.Diagnostics)
		if parsed.Expression == nil {
			t.Fatal("missing expression")
		}
		emmath.Linear(parsed.Expression, emmath.CharsetUnicode)
		emmath.Linear(parsed.Expression, emmath.CharsetASCII)
		box, err := emmath.Layout(parsed.Expression, interMetrics{}, bodyPx)
		if err != nil {
			if !errors.Is(err, geom.ErrOverflow) {
				t.Fatalf("layout error %v is not overflow", err)
			}
			return
		}
		checkBoxExtent(t, box)
	})
}
