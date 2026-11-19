package math_test

import (
	"strings"
	"testing"

	"pgregory.net/rapid"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	emmath "github.com/gosuda/elegant-mermaid/internal/math"
)

var (
	atomGlyphs = strings.Split("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-,.", "")
	atomGreek  = strings.Fields(`\alpha \beta \gamma \delta \epsilon \varepsilon \zeta \eta \theta \vartheta \iota \kappa \lambda \mu \nu \xi \pi \rho \sigma \tau \upsilon \phi \varphi \chi \psi \omega \Gamma \Delta \Theta \Lambda \Xi \Pi \Sigma \Upsilon \Phi \Psi \Omega`)
	operators  = strings.Fields(`\pm \times \div \cdot = \le \ge \ne \approx \to \leftarrow \Rightarrow \Leftrightarrow \infty`)
	spaces     = []string{`\,`, `\;`, `\quad `}
	fontNames  = []string{`\mathbf`, `\mathit`, `\mathrm`}
	delimiters = [][2]string{{"(", ")"}, {"[", "]"}, {`\{`, `\}`}, {"|", "|"}, {".", "."}}
	limitOps   = []string{`\sum `, `\prod `, `\lim `}
)

type termGenerator struct {
	t *rapid.T
}

func (g termGenerator) index(label string, n int) int {
	return rapid.IntRange(0, n-1).Draw(g.t, label)
}

func (g termGenerator) glyph() string {
	return atomGlyphs[g.index("glyph", len(atomGlyphs))]
}

func (g termGenerator) greek() string {
	return atomGreek[g.index("greek", len(atomGreek))] + " "
}

func (g termGenerator) simpleAtom() string {
	if g.index("simple-kind", 3) == 0 {
		return g.greek()
	}
	if g.index("simple-infty", 8) == 0 {
		return `\infty `
	}
	return g.glyph()
}

func (g termGenerator) simple() string {
	var out strings.Builder
	for range 1 + g.index("simple-length", 3) {
		out.WriteString(g.simpleAtom())
	}
	return out.String()
}

func (g termGenerator) atom(depth int) string {
	if depth > 0 && g.index("atom-kind", 4) == 0 {
		return "{" + g.term(depth-1) + "}"
	}
	return g.simpleAtom()
}

func (g termGenerator) term(depth int) string {
	var out strings.Builder
	for range 1 + g.index("term-length", 3) {
		out.WriteString(g.item(depth))
	}
	return out.String()
}

func leafItems() []func(g termGenerator, depth int) string {
	return []func(g termGenerator, depth int) string{
		func(g termGenerator, _ int) string { return g.glyph() },
		func(g termGenerator, _ int) string { return g.greek() },
		func(g termGenerator, _ int) string { return operators[g.index("operator", len(operators))] + " " },
		func(g termGenerator, _ int) string { return spaces[g.index("space", len(spaces))] },
		func(g termGenerator, _ int) string { return `\text{` + g.words() + `}` },
		func(g termGenerator, _ int) string { return g.atom(0) + `^{` + g.simple() + `}_{` + g.simple() + `}` },
		func(g termGenerator, _ int) string { return g.atom(0) + `_{` + g.simple() + `}` },
		func(g termGenerator, _ int) string { return `\int^{` + g.simple() + `}_{` + g.simple() + `}` },
	}
}

func nestedItems() []func(g termGenerator, depth int) string {
	return []func(g termGenerator, depth int) string{
		func(g termGenerator, d int) string { return "{" + g.term(d-1) + "}" },
		func(g termGenerator, d int) string { return `\frac{` + g.term(d-1) + `}{` + g.term(d-1) + `}` },
		func(g termGenerator, d int) string { return `\sqrt{` + g.term(d-1) + `}` },
		func(g termGenerator, d int) string { return `\sqrt[` + g.term(d-1) + `]{` + g.term(d-1) + `}` },
		func(g termGenerator, d int) string { return g.delimited(d) },
		func(g termGenerator, d int) string {
			return fontNames[g.index("font", len(fontNames))] + `{` + g.term(d-1) + `}`
		},
		func(g termGenerator, d int) string { return g.atom(d) + `^{` + g.term(d-1) + `}` },
		func(g termGenerator, d int) string { return g.atom(d) + `_{` + g.term(d-1) + `}` },
		func(g termGenerator, d int) string { return g.limits(d) },
		func(g termGenerator, d int) string { return `\int^{` + g.term(d-1) + `}` },
		func(g termGenerator, d int) string {
			return g.atom(d) + `^{` + g.term(d-1) + `}_{` + g.term(d-1) + `}`
		},
		func(g termGenerator, d int) string {
			return `\int^{` + g.term(d-1) + `}_{` + g.term(d-1) + `}`
		},
	}
}

func (g termGenerator) item(depth int) string {
	items := leafItems()
	if depth > 0 && g.index("nesting", 2) == 0 {
		items = nestedItems()
	}
	return items[g.index("item", len(items))](g, depth)
}

func (g termGenerator) delimited(depth int) string {
	pair := delimiters[g.index("delimiters", len(delimiters))]
	return `\left` + pair[0] + g.term(depth-1) + `\right` + pair[1]
}

func (g termGenerator) limits(depth int) string {
	out := limitOps[g.index("limit-op", len(limitOps))]
	scripts := 1 + g.index("limit-scripts", 3)
	if scripts&1 != 0 {
		out += `^{` + g.term(depth-1) + `}`
	}
	if scripts&2 != 0 {
		out += `_{` + g.term(depth-1) + `}`
	}
	return out
}

func (g termGenerator) words() string {
	alphabet := "abc xyz"
	var out strings.Builder
	for range 1 + g.index("words-length", 5) {
		out.WriteByte(alphabet[g.index("word-char", len(alphabet))])
	}
	return out.String()
}

func requireDisjointInsideBox(t *rapid.T, formula string, box emmath.Box) {
	bounds := box.Bounds()
	for i, leaf := range box.Leaves {
		inside, err := geom.Contains(bounds, leaf.Rect)
		if err != nil || !inside {
			t.Fatalf("leaf %d %+v lies outside box %+v in %q (err %v)", i, leaf.Rect, bounds, formula, err)
		}
		for j := i + 1; j < len(box.Leaves) && !leaf.Container; j++ {
			if box.Leaves[j].Container {
				continue
			}
			overlap, err := geom.Intersects(leaf.Rect, box.Leaves[j].Rect)
			if err != nil || overlap {
				t.Fatalf("leaves %d %+v and %d %+v overlap in %q (err %v)", i, leaf.Rect, j, box.Leaves[j].Rect, formula, err)
			}
		}
	}
}

func requireGlyphLeafBox(t *rapid.T, formula string, leaf emmath.Leaf) {
	advance, err := interMetrics{}.Advance(leaf.Weight, leaf.Codepoint)
	if err != nil {
		t.Fatalf("advance of %U in %q: %v", leaf.Codepoint, formula, err)
	}
	upem, err := interMetrics{}.Upem(leaf.Weight)
	if err != nil {
		t.Fatalf("upem in %q: %v", formula, err)
	}
	size := int64(leaf.Size)
	width := int32(ceilDiv(int64(advance)*size, int64(upem)))
	height := leaf.Size
	want := geom.Rect{X: leaf.Rect.X, Y: leaf.Rect.Y, W: width, H: height}
	if leaf.Rect != want {
		t.Fatalf("glyph %U in %q has box %+v, want advance width x (ascent+descent) %+v", leaf.Codepoint, formula, leaf.Rect, want)
	}
}

func TestMathLeafBoxes(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		g := termGenerator{t: t}
		formula := g.term(3)
		sizePx := int32(8 + g.index("size", 25))
		parsed := emmath.Parse(formula)
		if len(parsed.Diagnostics) != 0 {
			t.Fatalf("generated term %q is not well formed: %+v", formula, parsed.Diagnostics)
		}
		box, err := emmath.Layout(parsed.Expression, interMetrics{}, sizePx)
		if err != nil {
			t.Fatalf("layout of %q at %d px: %v", formula, sizePx, err)
		}
		requireDisjointInsideBox(t, formula, box)
		for _, leaf := range box.Leaves {
			if leaf.Kind == emmath.LeafGlyph {
				requireGlyphLeafBox(t, formula, leaf)
			}
		}
	})
}
