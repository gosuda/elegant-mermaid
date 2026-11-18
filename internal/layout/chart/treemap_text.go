package chart

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const treemapEllipsis = "..."

type treemapLabelKind uint8

const (
	treemapTitle treemapLabelKind = iota
	treemapName
	treemapValue
)

type treemapLabel struct {
	id, owner, text string
	kind            treemapLabelKind
	shown           string
	rect            geom.Rect
	size            int32
	align           scene.Align
	role            scene.TextRole
	style           string
	italic          bool
	ok              bool
}

type treemapStyle struct {
	role measure.Role
	size int64
}

func (p *treemapPlan) labelSpecs() []treemapLabel {
	var out []treemapLabel
	add := func(l treemapLabel) int {
		out = append(out, l)
		return len(out) - 1
	}
	if p.title != "" {
		add(treemapLabel{id: "title", owner: TreemapRootID, text: p.title, kind: treemapTitle})
	}
	for i := 1; i < len(p.nodes); i++ {
		n := &p.nodes[i]
		id := treemapBoxID(i)
		n.nameLabel, n.valueLabel = -1, -1
		if n.name != "" {
			n.nameLabel = add(treemapLabel{id: id + ".name", owner: id, text: n.name, kind: treemapName})
		}
		if n.valueText != "" {
			n.valueLabel = add(treemapLabel{id: id + ".value", owner: id, text: n.valueText, kind: treemapValue})
		}
	}
	return out
}

func (p *treemapPlan) dumpLabels() []scene.Label {
	out := make([]scene.Label, len(p.labels))
	for i, l := range p.labels {
		out[i] = scene.Label{ID: l.id, Owner: l.owner, Text: l.text, Rect: l.rect, Lines: []string{}}
		if l.ok {
			out[i].Lines = []string{l.shown}
		}
	}
	return out
}

func (p *treemapPlan) lineHeight(role measure.Role) int64 {
	if p.cell {
		return 1
	}
	return int64(role.LineHeightPx()) * 64
}

func (p *treemapPlan) textWidth(text string, s treemapStyle) (int64, error) {
	metric := measure.CellMetric()
	if !p.cell {
		metric = measure.Metric{Profile: measure.ProfileVector, SizePx: int32(s.size), Weight: s.role.Weight()}
	}
	w, err := metric.TextWidth(text)
	return int64(w), err
}

func (p *treemapPlan) fit(text string, avail int64, s treemapStyle) (shown string, width int64, ok bool, err error) {
	if text == "" {
		return "", 0, false, nil
	}
	if width, err = p.textWidth(text, s); err != nil {
		return "", 0, false, err
	}
	if width <= avail {
		return text, width, true, nil
	}
	return p.ellipsize(text, avail, s)
}

func (p *treemapPlan) ellipsize(text string, avail int64, s treemapStyle) (shown string, width int64, ok bool, err error) {
	if width, err = p.textWidth(treemapEllipsis, s); err != nil || width > avail {
		return "", 0, false, err
	}
	clusters := measure.Segment(text)
	prefix := func(k int) string {
		var b strings.Builder
		for _, c := range clusters[:k] {
			b.WriteString(c.Text)
		}
		return b.String() + treemapEllipsis
	}
	lo, hi := 0, len(clusters)-1
	for lo < hi {
		mid := (lo + hi + 1) / 2
		w, err := p.textWidth(prefix(mid), s)
		if err != nil {
			return "", 0, false, err
		}
		if w <= avail {
			lo = mid
		} else {
			hi = mid - 1
		}
	}
	shown = prefix(lo)
	width, err = p.textWidth(shown, s)
	return shown, width, err == nil, err
}

func (p *treemapPlan) put(l *treemapLabel, shown string, r rect, s treemapStyle) error {
	g, err := r.geom()
	if err != nil {
		return err
	}
	l.rect, l.shown, l.ok, l.size = g, shown, true, int32(s.size)
	return nil
}

func (p *treemapPlan) placeAll() error {
	for k := range p.labels {
		l := &p.labels[k]
		l.align, l.role, l.style = scene.AlignMiddle, scene.TextRoleLabel, "text"
		switch l.kind {
		case treemapTitle:
			l.role = scene.TextRoleTitle
		case treemapValue:
			l.role, l.style = scene.TextRoleBody, "text-muted"
		}
	}
	if p.title != "" {
		if err := p.placeTitle(&p.labels[0]); err != nil {
			return err
		}
	}
	for i := 1; i < len(p.nodes); i++ {
		place := p.placeLeaf
		if len(p.nodes[i].kids) > 0 {
			place = p.placeHeader
		}
		if err := place(i); err != nil {
			return err
		}
	}
	return nil
}

func (p *treemapPlan) placeTitle(l *treemapLabel) error {
	s := treemapStyle{measure.RoleTitle, int64(measure.RoleTitle.SizePx())}
	shown, w, ok, err := p.fit(l.text, p.c.width, s)
	if err != nil || !ok {
		return err
	}
	lh := p.lineHeight(s.role)
	return p.put(l, shown, rect{geom.FloorDiv(p.c.width-w, 2), geom.FloorDiv(p.c.titleBand-lh, 2), w, lh}, s)
}

func (p *treemapPlan) placeHeader(i int) error {
	n := &p.nodes[i]
	r := n.rect.rect()
	name := treemapStyle{measure.RoleLabel, p.c.headerLabelSize / 64}
	value := treemapStyle{measure.RoleBody, p.c.headerValueSize / 64}
	lh := p.lineHeight(measure.RoleLabel)
	top := p.c.headerBorder + geom.FloorDiv(p.c.header-p.c.headerBorder-lh, 2)
	if r.h <= top+lh {
		return nil
	}
	var valueW int64
	if n.valueLabel >= 0 {
		var err error
		if valueW, err = p.textWidth(p.labels[n.valueLabel].text, value); err != nil {
			return err
		}
	}
	reserve := p.c.valueInset + valueW + p.c.gap
	showValue := n.valueLabel >= 0 && valueW+p.c.valueInset+p.c.labelInset <= r.w &&
		(n.nameLabel < 0 || r.w-p.c.labelInset-reserve >= p.c.labelMin)
	avail := r.w - 2*p.c.labelInset
	if showValue {
		avail = r.w - p.c.labelInset - reserve
	}
	if err := p.placeHeaderName(n, rect{r.x + p.c.labelInset, r.y + top, avail, lh}, name); err != nil || !showValue {
		return err
	}
	l := &p.labels[n.valueLabel]
	l.align, l.italic = scene.AlignEnd, true
	return p.put(l, l.text, rect{r.x + r.w - p.c.valueInset - valueW, r.y + top, valueW, lh}, value)
}

func (p *treemapPlan) placeHeaderName(n *treemapNode, slot rect, s treemapStyle) error {
	if n.nameLabel < 0 {
		return nil
	}
	l := &p.labels[n.nameLabel]
	shown, w, ok, err := p.fit(l.text, slot.w, s)
	if err != nil || !ok {
		return err
	}
	l.align = scene.AlignStart
	return p.put(l, shown, rect{slot.x, slot.y, w, slot.h}, s)
}

func (p *treemapPlan) leafConsts() treemapLeafConsts {
	if int64(p.leaves) > p.c.dense {
		return p.c.thick
	}
	return p.c.sparse
}

func (p *treemapPlan) placeLeaf(i int) error {
	n := &p.nodes[i]
	if n.nameLabel < 0 {
		return nil
	}
	b, shows := p.leafBounds(n)
	if !shows {
		return nil
	}
	if p.cell {
		return p.placeLeafCell(n, b)
	}
	return p.placeLeafVector(n, b)
}

type leafBounds struct {
	r              rect
	availW, availH int64
	leaf           treemapLeafConsts
}

func (p *treemapPlan) leafBounds(n *treemapNode) (leafBounds, bool) {
	leaf := p.leafConsts()
	r := n.rect.rect()
	b := leafBounds{r: r, availW: r.w - 2*leaf.pad, availH: r.h - 2*leaf.pad, leaf: leaf}
	return b, b.availW >= leaf.minDisplay && b.availH >= leaf.minDisplay
}

func roundHalfUp(a, b int64) int64 { return geom.FloorDiv(2*a+b, 2*b) }

func (p *treemapPlan) valueSizePx(b leafBounds, labelPx int64) int64 {
	scaled := roundHalfUp(labelPx*p.c.valuePercent, 100)
	return max(b.leaf.valueMin/64, min(b.leaf.valueSize/64, scaled))
}

func (p *treemapPlan) fitLabelSize(name string, b leafBounds) (int64, error) {
	size, smallest := b.leaf.labelSize/64, b.leaf.labelMin/64
	for size > smallest {
		w, err := p.textWidth(name, treemapStyle{measure.RoleLabel, size})
		if err != nil {
			return 0, err
		}
		if w <= b.availW {
			break
		}
		size--
	}
	for size > smallest && size*64 > b.availH {
		size--
	}
	return size, nil
}

func (p *treemapPlan) placeLeafVector(n *treemapNode, b leafBounds) error {
	l := &p.labels[n.nameLabel]
	size, err := p.fitLabelSize(l.text, b)
	if err != nil {
		return err
	}
	name := treemapStyle{measure.RoleLabel, size}
	shown, w, ok, err := p.fit(l.text, b.availW, name)
	lh := p.lineHeight(measure.RoleLabel)
	if err != nil || !ok || lh > b.r.h {
		return err
	}
	value := treemapStyle{measure.RoleBody, p.valueSizePx(b, size)}
	pair := 2*lh + b.leaf.spacing
	valueW, showValue, err := p.valueFits(n, b, value, pair <= b.r.h)
	if err != nil {
		return err
	}
	top := b.r.y + geom.FloorDiv(b.r.h-lh, 2)
	if showValue {
		top = b.r.y + geom.FloorDiv(b.r.h-pair, 2)
	}
	if err = p.put(l, shown, rect{b.r.x + b.leaf.pad + geom.FloorDiv(b.availW-w, 2), top, w, lh}, name); err != nil || !showValue {
		return err
	}
	v := &p.labels[n.valueLabel]
	return p.put(v, v.text, rect{b.r.x + b.leaf.pad + geom.FloorDiv(b.availW-valueW, 2), top + lh + b.leaf.spacing, valueW, lh}, value)
}

func (p *treemapPlan) valueFits(n *treemapNode, b leafBounds, s treemapStyle, room bool) (int64, bool, error) {
	if n.valueLabel < 0 || !room {
		return 0, false, nil
	}
	w, err := p.textWidth(p.labels[n.valueLabel].text, s)
	return w, err == nil && w <= b.availW, err
}

func (p *treemapPlan) placeLeafCell(n *treemapNode, b leafBounds) error {
	name := treemapStyle{role: measure.RoleLabel}
	l := &p.labels[n.nameLabel]
	shown, w, ok, err := p.fit(l.text, b.availW, name)
	if err != nil || !ok {
		return err
	}
	value := treemapStyle{role: measure.RoleBody}
	pair := 2 + b.leaf.spacing
	valueW, showValue, err := p.valueFits(n, b, value, pair <= b.availH)
	if err != nil {
		return err
	}
	rows := int64(1)
	if showValue {
		rows = pair
	}
	top := b.r.y + b.leaf.pad + geom.FloorDiv(b.availH-rows, 2)
	if err = p.put(l, shown, rect{b.r.x + b.leaf.pad + geom.FloorDiv(b.availW-w, 2), top, w, 1}, name); err != nil || !showValue {
		return err
	}
	v := &p.labels[n.valueLabel]
	return p.put(v, v.text, rect{b.r.x + b.leaf.pad + geom.FloorDiv(b.availW-valueW, 2), top + 1 + b.leaf.spacing, valueW, 1}, value)
}

func itoa(n int) string { return strconv.Itoa(n) }
