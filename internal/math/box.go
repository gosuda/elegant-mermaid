package math

import (
	"errors"
	"sort"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

var ErrConstant = errors.New("math: missing layout constant")

type LeafKind uint8

const (
	LeafGlyph LeafKind = iota
	LeafRule
	LeafPath
)

type Weight uint8

const (
	WeightRegular Weight = iota
	WeightBold
)

func weightOf(style Font) Weight {
	if style == FontBold {
		return WeightBold
	}
	return WeightRegular
}

type Leaf struct {
	Kind      LeafKind
	Rect      geom.Rect
	Codepoint rune
	Weight    Weight
	Shear     bool
	Size      int32
	Points    []geom.Point
	Container bool
}

func (l Leaf) Baseline() int32 {
	return l.Rect.Y + l.Size
}

type Box struct {
	W, A, D int32
	Leaves  []Leaf
}

func (b Box) Bounds() geom.Rect {
	return geom.Rect{X: 0, Y: 0, W: b.W, H: b.A + b.D}
}

type Metrics interface {
	Upem(weight Weight) (int32, error)
	Advance(weight Weight, codepoint rune) (int32, error)
}

type constants struct {
	rule, axis, fracGap, supShift, subShift, scriptGap int64
	radGap, radSignW, delimW, bigopGap                 int64
	binopSpace, relopSpace, thin, medium, quad         int64
	scriptScale, bigopSize                             int64
}

type layouter struct {
	metrics Metrics
	em      int64
	k       constants
}

func roundHalfUp(a, b int64) int64 {
	return geom.FloorDiv(2*a+b, 2*b)
}

func ceilDiv(a, b int64) int64 {
	return geom.FloorDiv(a+b-1, b)
}

func centred(outer int64, inner int32) int64 {
	return geom.FloorDiv(outer-int64(inner), 2)
}

func narrow(value int64) (int32, error) {
	if value < int64(geom.I32Min) || value > int64(geom.I32Max) {
		return 0, geom.ErrOverflow
	}
	return int32(value), nil
}

func constant(name string) (int64, error) {
	key := "vector.math." + name
	index := sort.Search(len(gen.LayoutConst), func(i int) bool { return gen.LayoutConst[i].Name >= key })
	if index >= len(gen.LayoutConst) || gen.LayoutConst[index].Name != key {
		return 0, ErrConstant
	}
	return int64(gen.LayoutConst[index].Value), nil
}

type constantReader struct {
	em  int64
	err error
}

func (r *constantReader) raw(name string) int64 {
	value, err := constant(name)
	if err != nil && r.err == nil {
		r.err = err
	}
	return value
}

func (r *constantReader) length(name string) int64 {
	return roundHalfUp(r.raw(name)*r.em, 1000)
}

func loadConstants(em int64) (constants, error) {
	r := constantReader{em: em}
	k := constants{
		rule:        max(1, r.length("rule")),
		axis:        r.length("axis"),
		fracGap:     r.length("frac_gap"),
		supShift:    r.length("sup_shift"),
		subShift:    r.length("sub_shift"),
		scriptGap:   r.length("script_gap"),
		radGap:      r.length("rad_gap"),
		radSignW:    r.length("rad_sign_w"),
		delimW:      r.length("delim_w"),
		bigopGap:    r.length("bigop_gap"),
		binopSpace:  r.length("binop_space"),
		relopSpace:  r.length("relop_space"),
		thin:        r.length("thin_space"),
		medium:      r.length("medium_space"),
		quad:        r.length("quad"),
		scriptScale: r.raw("script_scale"),
		bigopSize:   r.length("bigop_scale"),
	}
	return k, r.err
}

func Layout(expression *Expr, metrics Metrics, sizePx int32) (Box, error) {
	if sizePx < 0 {
		return Box{}, geom.ErrDomain
	}
	em := int64(sizePx) * 64
	k, err := loadConstants(em)
	if err != nil {
		return Box{}, err
	}
	l := &layouter{metrics: metrics, em: em, k: k}
	return l.box(expression, em)
}

func (l *layouter) scriptSize(size int64) int64 {
	return roundHalfUp(l.k.scriptScale*size, 1000)
}

func finish(w, a, d int64) (Box, error) {
	wi, err := narrow(w)
	if err != nil {
		return Box{}, err
	}
	ai, err := narrow(a)
	if err != nil {
		return Box{}, err
	}
	di, err := narrow(d)
	if err != nil {
		return Box{}, err
	}
	return Box{W: wi, A: ai, D: di}, nil
}

func place(dst *Box, part Box, dx, baselineUp int64) error {
	top := int64(dst.A) - baselineUp - int64(part.A)
	moved, err := translateLeaves(part.Leaves, dx, top)
	if err != nil {
		return err
	}
	dst.Leaves = append(dst.Leaves, moved...)
	return nil
}

func translateLeaves(leaves []Leaf, dx, dy int64) ([]Leaf, error) {
	out := make([]Leaf, len(leaves))
	for i, leaf := range leaves {
		x, err := narrow(int64(leaf.Rect.X) + dx)
		if err != nil {
			return nil, err
		}
		y, err := narrow(int64(leaf.Rect.Y) + dy)
		if err != nil {
			return nil, err
		}
		leaf.Rect.X, leaf.Rect.Y = x, y
		if leaf.Points, err = translatePoints(leaf.Points, dx, dy); err != nil {
			return nil, err
		}
		out[i] = leaf
	}
	return out, nil
}

func translatePoints(points []geom.Point, dx, dy int64) ([]geom.Point, error) {
	var out []geom.Point
	for _, point := range points {
		x, err := narrow(int64(point.X) + dx)
		if err != nil {
			return nil, err
		}
		y, err := narrow(int64(point.Y) + dy)
		if err != nil {
			return nil, err
		}
		out = append(out, geom.Point{X: x, Y: y})
	}
	return out, nil
}

func (l *layouter) box(e *Expr, size int64) (Box, error) {
	switch e.Kind {
	case KindLiteral:
		return l.literal(e.Literal, size)
	case KindRow:
		return l.row(e.Children, size)
	case KindGroup, KindStyled, KindText:
		return l.box(e.Body, size)
	case KindSpace:
		return l.space(e.Space)
	case KindGlyph, KindLimit, KindSymbol:
		return l.atom(e, size)
	}
	return l.construct(e, size)
}

func (l *layouter) atom(e *Expr, size int64) (Box, error) {
	switch e.Kind {
	case KindGlyph:
		return l.glyph(e.Char, e.Font, size)
	case KindLimit:
		return l.limit(size)
	}
	return l.symbol(e, size)
}

func (l *layouter) construct(e *Expr, size int64) (Box, error) {
	switch e.Kind {
	case KindFraction:
		return l.fraction(e, size)
	case KindScripts:
		return l.scripts(e, size)
	case KindRadical:
		return l.radical(e, size)
	case KindDelimited:
		return l.delimited(e, size)
	}
	return Box{}, geom.ErrDomain
}

func fontCodepoint(logical rune) rune {
	for _, row := range gen.MathGlyphMappings {
		if rune(row.Codepoint) == logical {
			return rune(row.FontCodepoint)
		}
	}
	return logical
}

func (l *layouter) glyph(logical rune, style Font, size int64) (Box, error) {
	weight := weightOf(style)
	codepoint := fontCodepoint(logical)
	advance, err := l.metrics.Advance(weight, codepoint)
	if err != nil {
		return Box{}, err
	}
	upem, err := l.metrics.Upem(weight)
	if err != nil || upem <= 0 {
		return Box{}, geom.ErrDomain
	}
	box, err := finish(ceilDiv(int64(advance)*size, int64(upem)), size, 0)
	if err != nil {
		return Box{}, err
	}
	box.Leaves = []Leaf{{
		Kind:      LeafGlyph,
		Rect:      geom.Rect{W: box.W, H: box.A},
		Codepoint: codepoint,
		Weight:    weight,
		Shear:     style == FontItalic,
		Size:      box.A,
	}}
	return box, nil
}

func horizontal(parts []Box, gaps []int64) (Box, error) {
	xs := make([]int64, len(parts))
	var cursor int64
	var a, d int32
	for i, part := range parts {
		cursor += gaps[i]
		xs[i] = cursor
		cursor += int64(part.W)
		a, d = max(a, part.A), max(d, part.D)
	}
	box, err := finish(cursor, int64(a), int64(d))
	if err != nil {
		return Box{}, err
	}
	for i, part := range parts {
		if err := place(&box, part, xs[i], 0); err != nil {
			return Box{}, err
		}
	}
	return box, nil
}

func (l *layouter) glyphRun(text string, styleOf func(rune) Font, size int64) (Box, error) {
	var parts []Box
	for _, character := range text {
		glyph, err := l.glyph(character, styleOf(character), size)
		if err != nil {
			return Box{}, err
		}
		parts = append(parts, glyph)
	}
	return horizontal(parts, make([]int64, len(parts)))
}

func (l *layouter) limit(size int64) (Box, error) {
	return l.glyphRun("lim", func(rune) Font { return FontRoman }, size)
}

func (l *layouter) literal(text string, size int64) (Box, error) {
	return l.glyphRun(text, func(character rune) Font {
		if isASCIIAlpha(character) {
			return FontItalic
		}
		return FontRoman
	}, size)
}

func (l *layouter) space(space Space) (Box, error) {
	width := l.k.thin
	switch space {
	case SpaceMedium:
		width = l.k.medium
	case SpaceQuad:
		width = l.k.quad
	}
	return finish(width, 0, 0)
}

func (l *layouter) symbol(e *Expr, size int64) (Box, error) {
	if e.Class == ClassSum || e.Class == ClassProduct || e.Class == ClassIntegral {
		size = l.k.bigopSize
	}
	return l.glyph(e.Char, e.Font, size)
}

func (l *layouter) sideSpace(e *Expr) int64 {
	switch e.Kind {
	case KindSymbol:
		return l.symbolSpace(e.Class)
	case KindScripts:
		return l.sideSpace(e.Base)
	}
	return 0
}

func (l *layouter) symbolSpace(class SymbolClass) int64 {
	switch class {
	case ClassBinary:
		return l.k.binopSpace
	case ClassRelation:
		return l.k.relopSpace
	}
	return 0
}

func (l *layouter) row(children []*Expr, size int64) (Box, error) {
	parts := make([]Box, len(children))
	sides := make([]int64, len(children))
	for i, child := range children {
		box, err := l.box(child, size)
		if err != nil {
			return Box{}, err
		}
		parts[i], sides[i] = box, l.sideSpace(child)
	}
	gaps := make([]int64, len(children))
	for i := 1; i < len(children); i++ {
		gaps[i] = sides[i-1] + sides[i]
	}
	return horizontal(parts, gaps)
}

func (l *layouter) fraction(e *Expr, size int64) (Box, error) {
	numerator, err := l.box(e.Numerator, size)
	if err != nil {
		return Box{}, err
	}
	denominator, err := l.box(e.Denominator, size)
	if err != nil {
		return Box{}, err
	}
	width := max(int64(numerator.W), int64(denominator.W)) + 2*l.k.scriptGap
	barBottom := l.k.axis - l.k.rule/2
	barTop := barBottom + l.k.rule
	numeratorBase := barTop + l.k.fracGap + int64(numerator.D)
	denominatorBase := barBottom - l.k.fracGap - int64(denominator.A)
	ascent := numeratorBase + int64(numerator.A)
	box, err := finish(width, ascent, int64(denominator.D)-denominatorBase)
	if err != nil {
		return Box{}, err
	}
	barY, err := narrow(ascent - barTop)
	if err != nil {
		return Box{}, err
	}
	barW, err := narrow(width)
	if err != nil {
		return Box{}, err
	}
	barH, err := narrow(l.k.rule)
	if err != nil {
		return Box{}, err
	}
	box.Leaves = []Leaf{{Kind: LeafRule, Rect: geom.Rect{Y: barY, W: barW, H: barH}, Container: true}}
	if err := place(&box, numerator, centred(width, numerator.W), numeratorBase); err != nil {
		return Box{}, err
	}
	return box, place(&box, denominator, centred(width, denominator.W), denominatorBase)
}

type script struct {
	box  Box
	base int64
}

func (l *layouter) optional(e *Expr, size int64) (*Box, error) {
	if e == nil {
		return nil, nil
	}
	box, err := l.box(e, size)
	return &box, err
}

func (l *layouter) scripts(e *Expr, size int64) (Box, error) {
	switch {
	case e.Base.Kind == KindSymbol && (e.Base.Class == ClassSum || e.Base.Class == ClassProduct):
		return l.bigopLimits(e)
	case e.Base.Kind == KindSymbol && e.Base.Class == ClassIntegral:
		return l.rightScripts(e, l.k.bigopSize)
	case e.Base.Kind == KindLimit:
		return l.limitScripts(e, size)
	}
	return l.rightScripts(e, size)
}

func (l *layouter) rightScripts(e *Expr, baseSize int64) (Box, error) {
	base, err := l.box(e.Base, baseSize)
	if err != nil {
		return Box{}, err
	}
	sup, err := l.optional(e.Superscript, l.scriptSize(baseSize))
	if err != nil {
		return Box{}, err
	}
	sub, err := l.optional(e.Subscript, l.scriptSize(baseSize))
	if err != nil {
		return Box{}, err
	}
	var scripts []script
	if sup != nil {
		scripts = append(scripts, script{box: *sup, base: l.k.supShift})
	}
	if sub != nil {
		scripts = append(scripts, script{box: *sub, base: l.subBase(sup, sub)})
	}
	return l.attach(base, scripts)
}

func (l *layouter) subBase(sup, sub *Box) int64 {
	if sup == nil {
		return -l.k.subShift
	}
	return min(-l.k.subShift, l.k.supShift-int64(sup.D)-int64(sub.A))
}

func (l *layouter) attach(base Box, scripts []script) (Box, error) {
	width, ascent, descent := int64(0), int64(base.A), int64(base.D)
	for _, s := range scripts {
		width = max(width, int64(s.box.W))
		ascent = max(ascent, s.base+int64(s.box.A))
		descent = max(descent, int64(s.box.D)-s.base)
	}
	x := int64(base.W) + l.k.scriptGap
	box, err := finish(x+width, ascent, descent)
	if err != nil {
		return Box{}, err
	}
	if err := place(&box, base, 0, 0); err != nil {
		return Box{}, err
	}
	for _, s := range scripts {
		if err := place(&box, s.box, x, s.base); err != nil {
			return Box{}, err
		}
	}
	return box, nil
}

func (l *layouter) bigopLimits(e *Expr) (Box, error) {
	glyph, err := l.symbol(e.Base, l.em)
	if err != nil {
		return Box{}, err
	}
	size := l.scriptSize(l.k.bigopSize)
	above, err := l.optional(e.Superscript, size)
	if err != nil {
		return Box{}, err
	}
	below, err := l.optional(e.Subscript, size)
	if err != nil {
		return Box{}, err
	}
	var limits []script
	if above != nil {
		limits = append(limits, script{box: *above, base: int64(glyph.A) + l.k.bigopGap + int64(above.D)})
	}
	if below != nil {
		limits = append(limits, script{box: *below, base: -(l.k.bigopGap + int64(below.A))})
	}
	return l.stack(glyph, limits)
}

func (l *layouter) stack(base Box, limits []script) (Box, error) {
	width, ascent, descent := int64(base.W), int64(base.A), int64(base.D)
	for _, s := range limits {
		width = max(width, int64(s.box.W))
		ascent = max(ascent, s.base+int64(s.box.A))
		descent = max(descent, int64(s.box.D)-s.base)
	}
	box, err := finish(width, ascent, descent)
	if err != nil {
		return Box{}, err
	}
	if err := place(&box, base, centred(width, base.W), 0); err != nil {
		return Box{}, err
	}
	for _, s := range limits {
		if err := place(&box, s.box, centred(width, s.box.W), s.base); err != nil {
			return Box{}, err
		}
	}
	return box, nil
}

func (l *layouter) limitScripts(e *Expr, size int64) (Box, error) {
	base, err := l.box(e.Base, size)
	if err != nil {
		return Box{}, err
	}
	var parts []Box
	for _, content := range []*Expr{e.Superscript, e.Subscript} {
		part, err := l.optional(content, l.scriptSize(size))
		if err != nil {
			return Box{}, err
		}
		if part != nil {
			parts = append(parts, *part)
		}
	}
	gaps := make([]int64, len(parts))
	for i := 1; i < len(parts); i++ {
		gaps[i] = l.k.scriptGap
	}
	row, err := horizontal(parts, gaps)
	if err != nil {
		return Box{}, err
	}
	return l.stack(base, []script{{box: row, base: -(l.k.bigopGap + int64(row.A))}})
}
