package tree

import "github.com/gosuda/elegant-mermaid/internal/geom"

const (
	branchMid  = "├── "
	branchLast = "└── "
	trunkOpen  = "│   "
	trunkEnd   = "    "
)

type ViewRow struct {
	Parent     int
	LabelWidth int32
	DescWidth  int32
	HasDesc    bool
	HasIcon    bool
}

type ViewMetrics struct {
	RowIndent, PaddingX, PaddingY, TextHeight int32
	IconSize, IconGap, DescGap                int32
	Thickness, Margin                         int32
}

type ViewLayout struct {
	Canvas geom.Size
	Boxes  []geom.Rect
	Depth  []int
	IconX  []int32
	LabelX []int32
	DescX  int32
	Right  int32
	Routes [][]geom.Point
}

type viewBuilder struct {
	rows     []ViewRow
	m        ViewMetrics
	depth    []int
	height   int64
	step     int64
	iconSpan int64
}

func TreeView(rows []ViewRow, m ViewMetrics) (ViewLayout, error) {
	b, err := newViewBuilder(rows, m)
	if err != nil {
		return ViewLayout{}, err
	}
	return b.layout()
}

func lastChildren(rows []ViewRow) []int {
	last := make([]int, len(rows))
	for i := range last {
		last[i] = NoParent
	}
	for i := 1; i < len(rows); i++ {
		if p := rows[i].Parent; p >= 0 && p < i {
			last[p] = i
		}
	}
	return last
}

func newViewBuilder(rows []ViewRow, m ViewMetrics) (*viewBuilder, error) {
	if len(rows) == 0 || rows[0].Parent != NoParent || m.TextHeight < 1 {
		return nil, ErrInvalid
	}
	if !validViewSpacing(m) {
		return nil, ErrInvalid
	}
	b := &viewBuilder{rows: rows, m: m, depth: make([]int, len(rows))}
	for i := 1; i < len(rows); i++ {
		p := rows[i].Parent
		if p < 0 || p >= i || rows[i].LabelWidth < 0 || rows[i].DescWidth < 0 {
			return nil, ErrInvalid
		}
		b.depth[i] = b.depth[p] + 1
	}
	b.height = int64(m.TextHeight) + 2*int64(m.PaddingY)
	b.step = int64(m.RowIndent) + int64(m.PaddingX)
	b.iconSpan = int64(m.IconSize) + int64(m.IconGap)
	return b, nil
}

func validViewSpacing(m ViewMetrics) bool {
	for _, v := range []int32{m.RowIndent, m.PaddingX, m.PaddingY, m.IconSize, m.IconGap, m.DescGap, m.Thickness, m.Margin} {
		if v < 0 {
			return false
		}
	}
	return true
}

func (b *viewBuilder) indent(i int) int64 { return int64(b.depth[i]) * b.step }

func (b *viewBuilder) slot(i int) int64 {
	if b.rows[i].HasIcon {
		return b.iconSpan
	}
	return 0
}

func (b *viewBuilder) labelX(i int) int64 { return b.indent(i) + int64(b.m.PaddingX) + b.slot(i) }

func (b *viewBuilder) width(i int) int64 {
	return max(int64(b.rows[i].LabelWidth)+2*int64(b.m.PaddingX)+b.slot(i), 1)
}

func (b *viewBuilder) extent() (right, descX int64) {
	for i := range b.rows {
		right = max(right, b.indent(i)+b.width(i))
		descX = max(descX, b.labelX(i)+int64(b.rows[i].LabelWidth)+int64(b.m.DescGap))
	}
	for _, r := range b.rows {
		if r.HasDesc {
			right = max(right, descX+int64(r.DescWidth)+int64(b.m.PaddingX))
		}
	}
	return right, descX
}

func (b *viewBuilder) layout() (ViewLayout, error) {
	n := len(b.rows)
	right, descX := b.extent()
	margin := int64(b.m.Margin)
	w, h := right+2*margin, int64(n)*b.height+2*margin
	if w > geom.CoordLimit || h > geom.CoordLimit {
		return ViewLayout{}, geom.ErrOverflow
	}
	out := ViewLayout{
		Canvas: geom.Size{W: int32(w), H: int32(h)},
		Boxes:  make([]geom.Rect, n), Depth: b.depth, IconX: make([]int32, n), LabelX: make([]int32, n),
		DescX: int32(descX + margin), Right: int32(right + margin),
		Routes: make([][]geom.Point, n),
	}
	for i := range b.rows {
		y := int64(i)*b.height + margin
		out.Boxes[i] = geom.Rect{X: int32(b.indent(i) + margin), Y: int32(y), W: int32(b.width(i)), H: int32(b.height)}
		out.IconX[i] = int32(b.indent(i) + int64(b.m.PaddingX) + margin)
		out.LabelX[i] = int32(b.labelX(i) + margin)
		out.Routes[i] = b.route(i, margin)
	}
	return out, nil
}

func (b *viewBuilder) route(i int, margin int64) []geom.Point {
	p := b.rows[i].Parent
	if p == NoParent {
		return nil
	}
	spineX := b.indent(p) + int64(b.m.PaddingX) + margin
	bottom := int64(p+1)*b.height + margin
	mid := int64(i)*b.height + margin + geom.FloorDiv(b.height, 2)
	end := geom.Point{X: int32(b.indent(i) + margin), Y: int32(mid)}
	points := []geom.Point{{X: int32(spineX), Y: int32(bottom)}, {X: int32(spineX), Y: int32(mid)}, end}
	if bottom == mid {
		points = points[1:]
	}
	return points
}

func TreePrefixes(rows []ViewRow) []string {
	last := lastChildren(rows)
	prefixes := make([]string, len(rows))
	trunk := make([]string, len(rows))
	for i := 1; i < len(rows); i++ {
		p := rows[i].Parent
		own, next := branchMid, trunkOpen
		if last[p] == i {
			own, next = branchLast, trunkEnd
		}
		prefixes[i] = trunk[p] + own
		trunk[i] = trunk[p] + next
	}
	return prefixes
}
