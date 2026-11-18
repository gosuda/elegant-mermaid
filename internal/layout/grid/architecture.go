package grid

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type ArchNode struct {
	Parent   int
	Junction bool
	Icon     geom.Size
	Label    geom.Size
}

type ArchGroup struct {
	Parent int
	Title  geom.Size
	Icon   bool
}

type ArchEdge struct {
	From, To         int
	FromSide, ToSide geom.Side
	Label            geom.Size
}

type ArchAlign struct {
	Column  bool
	Members []int
}

type ArchInput struct {
	Nodes  []ArchNode
	Groups []ArchGroup
	Edges  []ArchEdge
	Aligns []ArchAlign
}

type ArchParams struct {
	PitchX, PitchY      int32
	LabelWrap           int32
	IconW, IconH        int32
	Padding, LineHeight int32
	Badge               int32
	Inset, LabelGap     int32
	Thickness, Margin   int32
	Gutter              int32
	Fuel, RingCap       int32
}

type ArchLayout struct {
	Boxes      []geom.Rect
	Icons      []geom.Rect
	Labels     []geom.Rect
	Frames     []geom.Rect
	Titles     []geom.Rect
	GroupIcons []geom.Rect
	Routes     [][]geom.Point
	EdgeLabels []geom.Rect
	Canvas     geom.Size
	Budget     bool
}

type cell struct{ x, y int64 }

type pt struct{ x, y int64 }

type span struct{ x0, y0, x1, y1 int64 }

func (r span) overlaps(o span) bool {
	return max(r.x0, o.x0) < min(r.x1, o.x1) && max(r.y0, o.y0) < min(r.y1, o.y1)
}

func (r span) union(o span) span {
	return span{min(r.x0, o.x0), min(r.y0, o.y0), max(r.x1, o.x1), max(r.y1, o.y1)}
}

func (r span) strictlyInside(o span) bool {
	return r.x0 > o.x0 && r.x1 < o.x1 && r.y0 > o.y0 && r.y1 < o.y1
}

func (r span) inflate(d int64) span { return span{r.x0 - d, r.y0 - d, r.x1 + d, r.y1 + d} }

func (r span) shift(dx, dy int64) span { return span{r.x0 + dx, r.y0 + dy, r.x1 + dx, r.y1 + dy} }

func sized(x, y int64, s geom.Size) span { return span{x, y, x + int64(s.W), y + int64(s.H)} }

type archBuilder struct {
	in          ArchInput
	p           ArchParams
	real        int
	total       int
	parent      []int
	px, py, top int64
	shift       int64
	childGroups [][]int
	childNodes  [][]int
	firstNode   []int
	alignsOf    [][]int
	lifted      [][]liftedEdge
	local       []cell
	localGroup  []cell
	rel         []span
	pos         []cell
	frame       []span
	pops        int64
	budget      bool
	boxes       []span
	icons       []span
	labels      []span
	titles      []span
	badges      []span
	routes      [][]pt
}

func Architecture(in ArchInput, p ArchParams) (ArchLayout, error) {
	b := &archBuilder{in: in, p: p}
	if err := b.prepare(); err != nil {
		return ArchLayout{}, err
	}
	b.place()
	b.geometry()
	b.route()
	return b.finish()
}

func (b *archBuilder) prepare() error {
	if err := b.validate(); err != nil {
		return err
	}
	b.virtual()
	b.index()
	b.pitch()
	return nil
}

func (b *archBuilder) validate() error {
	p := b.p
	if !validArchPitch(p) || !validArchSpacing(p) || !validArchLimits(p) {
		return geom.ErrDomain
	}
	if !b.validGroups() || !b.validNodes() || !b.validEdges() || !b.validAligns() {
		return geom.ErrDomain
	}
	return nil
}

func (b *archBuilder) validGroups() bool {
	for i, g := range b.in.Groups {
		if g.Parent < -1 || g.Parent >= i || g.Title.W < 0 || g.Title.H < 0 {
			return false
		}
	}
	return true
}

func (b *archBuilder) validNodes() bool {
	for _, n := range b.in.Nodes {
		if n.Parent < -1 || n.Parent >= len(b.in.Groups) || n.Icon.W <= 0 || n.Icon.H <= 0 || n.Label.W < 0 || n.Label.H < 0 {
			return false
		}
	}
	return true
}

func (b *archBuilder) validEdges() bool {
	for _, e := range b.in.Edges {
		if !b.validEdge(e) {
			return false
		}
	}
	return true
}

func (b *archBuilder) validAligns() bool {
	for _, a := range b.in.Aligns {
		for _, m := range a.Members {
			if m < 0 || m >= len(b.in.Nodes) {
				return false
			}
		}
	}
	return true
}

func validArchLimits(p ArchParams) bool {
	return p.Fuel >= 0 && p.RingCap >= 0 && (p.Gutter == 0 || p.Gutter == 1)
}

func validArchPitch(p ArchParams) bool {
	return p.PitchX > 0 && p.PitchY > 0 && p.IconW > 0 && p.IconH > 0
}

func validArchSpacing(p ArchParams) bool {
	return p.Padding >= 0 && p.LineHeight >= 0 && p.Badge >= 0 && p.Inset >= 0 && p.LabelGap >= 0 && p.Thickness >= 0 && p.Margin >= 0
}

func (b *archBuilder) validEdge(e ArchEdge) bool {
	n := len(b.in.Nodes)
	return e.From >= 0 && e.From < n && e.To >= 0 && e.To < n && e.Label.W >= 0 && e.Label.H >= 0 &&
		e.FromSide >= geom.SideTop && e.FromSide <= geom.SideRight && e.ToSide >= geom.SideTop && e.ToSide <= geom.SideRight
}

func (b *archBuilder) virtual() {
	b.real = len(b.in.Nodes)
	b.parent = make([]int, 0, b.real+len(b.in.Groups))
	used := make([]bool, len(b.in.Groups))
	for _, n := range b.in.Nodes {
		b.parent = append(b.parent, n.Parent)
		if n.Parent >= 0 {
			used[n.Parent] = true
		}
	}
	for _, g := range b.in.Groups {
		if g.Parent >= 0 {
			used[g.Parent] = true
		}
	}
	for g := range b.in.Groups {
		if !used[g] {
			b.parent = append(b.parent, g)
		}
	}
	b.total = len(b.parent)
}

func (b *archBuilder) index() {
	b.childGroups = make([][]int, len(b.in.Groups)+1)
	b.childNodes = make([][]int, len(b.in.Groups)+1)
	for g, entry := range b.in.Groups {
		b.childGroups[entry.Parent+1] = append(b.childGroups[entry.Parent+1], g)
	}
	for v, parent := range b.parent {
		b.childNodes[parent+1] = append(b.childNodes[parent+1], v)
	}
	b.firstNode = make([]int, len(b.in.Groups))
	for g := len(b.in.Groups) - 1; g >= 0; g-- {
		first := b.total + g
		for _, w := range b.childNodes[g+1] {
			first = min(first, w)
		}
		for _, s := range b.childGroups[g+1] {
			first = min(first, b.firstNode[s])
		}
		b.firstNode[g] = first
	}
	b.alignsOf = make([][]int, b.total)
	for i, a := range b.in.Aligns {
		for _, m := range a.Members {
			b.alignsOf[m] = append(b.alignsOf[m], i)
		}
	}
}

func (b *archBuilder) pitch() {
	p := b.p
	iw, ih := int64(p.IconW), int64(p.IconH)
	b.shift = int64(p.Gutter)
	var labelW, labelH, edgeW, edgeH int64
	for _, n := range b.in.Nodes {
		labelW, labelH = max(labelW, int64(n.Label.W)), max(labelH, int64(n.Label.H))
	}
	for _, e := range b.in.Edges {
		edgeW, edgeH = max(edgeW, int64(e.Label.W)), max(edgeH, int64(e.Label.H))
	}
	pitchX, pitchY := int64(p.PitchX), int64(p.PitchY)
	px := max(pitchX, iw+b.shift, labelW+pitchX-int64(p.LabelWrap))
	if edgeW > 0 {
		px = max(px, max(iw, labelW)+b.shift+2*(int64(p.Thickness)+int64(p.LabelGap)+edgeW))
	}
	top0 := max(0, geom.FloorDiv(pitchY-ih, 2))
	top := top0
	if edgeH > 0 {
		top = max(top, int64(p.Thickness)+int64(p.LabelGap)+edgeH)
	}
	tail := max(0, pitchY-top0-ih)
	if labelH > 0 {
		tail = labelH + int64(p.Thickness) + max(b.shift, max(0, pitchY-top0-ih-int64(p.LineHeight)))
	}
	b.px, b.top, b.py = px, top, max(pitchY, top+ih+tail)
}

func (b *archBuilder) frameOf(g int, inner span) span {
	entry := b.in.Groups[g]
	pad, inset, line, badge := int64(b.p.Padding), int64(b.p.Inset), int64(b.p.LineHeight), int64(b.p.Badge)
	head := int64(entry.Title.H)
	need := int64(0)
	if entry.Title.W > 0 || entry.Icon {
		need = 2*inset + int64(entry.Title.W)
	}
	if entry.Icon {
		head = max(head, badge)
		need += badge + inset
	}
	f := span{inner.x0 - pad, inner.y0 - max(pad+line, 2*inset+head), inner.x1 + pad, inner.y1 + pad}
	f.x1 = max(f.x1, f.x0+need)
	return f
}
