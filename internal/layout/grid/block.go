package grid

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

const (
	maxTracks = 1 << 14
	maxDepth  = 66
)

type Kind uint8

const (
	KindLeaf Kind = iota
	KindSpace
	KindComposite
)

type Box struct {
	Parent  int
	Kind    Kind
	Span    int32
	Columns int32
	Size    geom.Size
}

type Edge struct {
	From, To int
	Label    geom.Size
}

type Input struct {
	Columns int32
	Boxes   []Box
	Edges   []Edge
}

type Params struct {
	Padding       int32
	BendCost      int32
	LineThickness int32
}

type Layout struct {
	Rects  []geom.Rect
	Routes [][]geom.Point
	Labels []geom.Rect
	Canvas geom.Size
}

type plan struct {
	order  []int
	col    []int64
	row    []int64
	eff    []int64
	ncols  int64
	nrows  int64
	unit   int64
	rows   []int64
	width  int64
	height int64
}

type builder struct {
	in       Input
	p        Params
	gapX     int64
	gapY     int64
	children [][]int
	plans    []plan
	rects    []geom.Rect
	vlines   []int64
	hlines   []int64
}

func Block(in Input, p Params) (Layout, error) {
	b := &builder{in: in, p: p}
	if err := b.validate(); err != nil {
		return Layout{}, err
	}
	b.gaps()
	root := len(in.Boxes)
	b.plans = make([]plan, root+1)
	b.rects = make([]geom.Rect, root+1)
	if _, _, err := b.measure(root, 0); err != nil {
		return Layout{}, err
	}
	canvas := geom.Rect{W: int32(b.plans[root].width), H: int32(b.plans[root].height)}
	if err := b.place(root, canvas); err != nil {
		return Layout{}, err
	}
	routes, labels, err := b.connect(&canvas)
	if err != nil {
		return Layout{}, err
	}
	b.rects[root] = canvas
	return Layout{Rects: b.rects, Routes: routes, Labels: labels, Canvas: geom.Size{W: canvas.W, H: canvas.H}}, nil
}

func (b *builder) validate() error {
	n := len(b.in.Boxes)
	if b.p.Padding < 0 {
		return geom.ErrDomain
	}
	b.children = make([][]int, n+1)
	for i := range b.in.Boxes {
		slot, err := b.slot(i)
		if err != nil {
			return err
		}
		b.children[slot] = append(b.children[slot], i)
	}
	for _, e := range b.in.Edges {
		if !e.valid(n) {
			return geom.ErrDomain
		}
	}
	return nil
}

func (e Edge) valid(boxes int) bool {
	return e.From >= 0 && e.From < boxes && e.To >= 0 && e.To < boxes && e.Label.W >= 0 && e.Label.H >= 0
}

func (b *builder) slot(i int) (int, error) {
	n, box := len(b.in.Boxes), b.in.Boxes[i]
	if box.Parent < -1 || box.Parent >= n || box.Parent == i || box.Size.W < 0 || box.Size.H < 0 {
		return 0, geom.ErrDomain
	}
	if box.Parent < 0 {
		return n, nil
	}
	if b.in.Boxes[box.Parent].Kind != KindComposite {
		return 0, geom.ErrDomain
	}
	return box.Parent, nil
}

func (b *builder) gaps() {
	var lw, lh int64
	for _, e := range b.in.Edges {
		lw, lh = max(lw, int64(e.Label.W)), max(lh, int64(e.Label.H))
	}
	corridor := int64(b.p.Padding)
	if len(b.in.Edges) > 0 {
		corridor *= 2
	}
	b.gapX, b.gapY = corridor, corridor
	if lw > 0 {
		b.gapX += lw
	}
	if lh > 0 {
		b.gapY += lh
	}
}

func ceilDiv(a, b int64) int64 { return geom.FloorDiv(a+b-1, b) }

func product(a, b int64) (int64, error) {
	if a == 0 || b == 0 {
		return 0, nil
	}
	if a > int64(geom.CoordLimit)/b {
		return 0, geom.ErrOverflow
	}
	return a * b, nil
}

func within(v int64) (int64, error) {
	if v < 0 || v > int64(geom.CoordLimit) {
		return 0, geom.ErrOverflow
	}
	return v, nil
}

func (b *builder) measure(i, depth int) (int64, int64, error) {
	root := len(b.in.Boxes)
	if i != root && b.in.Boxes[i].Kind != KindComposite {
		return int64(b.in.Boxes[i].Size.W), int64(b.in.Boxes[i].Size.H), nil
	}
	if depth > maxDepth {
		return 0, 0, geom.ErrDomain
	}
	pl, err := b.tracks(i, depth)
	if err != nil {
		return 0, 0, err
	}
	b.plans[i] = pl
	return pl.width, pl.height, nil
}

func (b *builder) columnLimit(i int) int64 {
	if i == len(b.in.Boxes) {
		return int64(max(b.in.Columns, 0))
	}
	return int64(max(b.in.Boxes[i].Columns, 0))
}

func effective(span int32) int64 { return max(int64(span), 1) }

func (b *builder) tracks(i, depth int) (plan, error) {
	pl := plan{order: b.children[i]}
	columns := b.columnLimit(i)
	var pos int64
	widths := make([]int64, len(pl.order))
	heights := make([]int64, len(pl.order))
	for k, c := range pl.order {
		w, h, err := b.measure(c, depth+1)
		if err != nil {
			return plan{}, err
		}
		span := effective(b.in.Boxes[c].Span)
		col, row := pos, int64(0)
		if columns > 0 {
			col, row = pos%columns, pos/columns
			span = min(span, columns-col)
		}
		pl.col, pl.row, pl.eff = append(pl.col, col), append(pl.row, row), append(pl.eff, span)
		pl.ncols, pl.nrows = max(pl.ncols, col+span), max(pl.nrows, row+1)
		if b.in.Boxes[c].Kind != KindSpace {
			widths[k], heights[k] = w, h
		}
		pos += span
	}
	if pl.ncols > maxTracks || pl.nrows > maxTracks {
		return plan{}, geom.ErrOverflow
	}
	return pl, b.size(&pl, widths, heights)
}

func (b *builder) size(pl *plan, widths, heights []int64) error {
	for k := range pl.order {
		pl.unit = max(pl.unit, ceilDiv(widths[k], pl.eff[k]))
	}
	pl.rows = make([]int64, pl.nrows)
	for k := range pl.order {
		pl.rows[pl.row[k]] = max(pl.rows[pl.row[k]], heights[k])
	}
	body, err := product(pl.ncols, pl.unit)
	if err != nil {
		return err
	}
	margins, err := product(pl.ncols+1, b.gapX)
	if err != nil {
		return err
	}
	if pl.width, err = within(body + margins); err != nil {
		return err
	}
	var rows int64
	for _, h := range pl.rows {
		rows += h
	}
	spacing, err := product(pl.nrows+1, b.gapY)
	if err != nil {
		return err
	}
	pl.height, err = within(rows + spacing)
	return err
}

func (b *builder) place(i int, frame geom.Rect) error {
	pl := b.plans[i]
	pad := int64(b.p.Padding)
	for j := int64(0); j <= pl.ncols; j++ {
		b.vlines = append(b.vlines, int64(frame.X)+j*(pl.unit+b.gapX)+pad)
	}
	rowTop := make([]int64, pl.nrows+1)
	rowTop[0] = int64(frame.Y)
	for r := int64(0); r < pl.nrows; r++ {
		rowTop[r+1] = rowTop[r] + pl.rows[r] + b.gapY
		b.hlines = append(b.hlines, rowTop[r]+pad)
	}
	b.hlines = append(b.hlines, rowTop[pl.nrows]+pad)
	for k, c := range pl.order {
		x := int64(frame.X) + b.gapX + pl.col[k]*(pl.unit+b.gapX)
		w := pl.unit*pl.eff[k] + b.gapX*(pl.eff[k]-1)
		y, h := rowTop[pl.row[k]]+b.gapY, pl.rows[pl.row[k]]
		if y+h > geom.CoordLimit || x+w > geom.CoordLimit {
			return geom.ErrOverflow
		}
		b.rects[c] = geom.Rect{X: int32(x), Y: int32(y), W: int32(w), H: int32(h)}
		if b.in.Boxes[c].Kind == KindComposite {
			if err := b.place(c, b.rects[c]); err != nil {
				return err
			}
		}
	}
	return nil
}

func sortedUnique(values []int64) []int32 {
	slices.Sort(values)
	values = slices.Compact(values)
	out := make([]int32, len(values))
	for k, v := range values {
		out[k] = int32(v)
	}
	return out
}
