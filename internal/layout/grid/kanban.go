package grid

import "github.com/gosuda/elegant-mermaid/internal/geom"

type KanbanSection struct {
	LabelHeight int32
}

type KanbanCard struct {
	Section int
	Height  int32
}

type KanbanInput struct {
	Sections []KanbanSection
	Cards    []KanbanCard
}

type KanbanParams struct {
	SectionWidth     int32
	Gutter           int32
	SectionGap       int32
	CardGap          int32
	Padding          int32
	Border           int32
	LabelBandMin     int32
	SectionMinHeight int32
}

type KanbanLayout struct {
	Sections []geom.Rect
	Labels   []geom.Rect
	Cards    []geom.Rect
	Canvas   geom.Size
}

func Kanban(in KanbanInput, p KanbanParams) (KanbanLayout, error) {
	if err := validateKanban(in, p); err != nil {
		return KanbanLayout{}, err
	}
	band := int64(p.LabelBandMin)
	for _, s := range in.Sections {
		band = max(band, int64(s.LabelHeight)+int64(p.Border))
	}
	k := kanbanBuilder{in: in, p: p, band: band, cardWidth: int64(p.SectionWidth) - geom.FloorDiv(3*int64(p.Gutter), 2)}
	if k.cardWidth <= 0 {
		return KanbanLayout{}, geom.ErrDomain
	}
	return k.place()
}

func validateKanban(in KanbanInput, p KanbanParams) error {
	for _, v := range []int32{p.SectionWidth, p.Gutter, p.SectionGap, p.CardGap, p.Padding, p.Border, p.LabelBandMin, p.SectionMinHeight} {
		if v < 0 {
			return geom.ErrDomain
		}
	}
	for _, s := range in.Sections {
		if s.LabelHeight < 0 {
			return geom.ErrDomain
		}
	}
	for _, c := range in.Cards {
		if c.Section < 0 || c.Section >= len(in.Sections) || c.Height < 0 {
			return geom.ErrDomain
		}
	}
	return nil
}

type kanbanBuilder struct {
	in        KanbanInput
	p         KanbanParams
	band      int64
	cardWidth int64
}

func (k *kanbanBuilder) place() (KanbanLayout, error) {
	n := len(k.in.Sections)
	out := KanbanLayout{Sections: make([]geom.Rect, n), Labels: make([]geom.Rect, n), Cards: make([]geom.Rect, len(k.in.Cards))}
	pad, width := int64(k.p.Padding), int64(k.p.SectionWidth)
	cursor := make([]int64, n)
	for s := range cursor {
		cursor[s] = k.band
	}
	inset := geom.FloorDiv(width-k.cardWidth, 2)
	for i, c := range k.in.Cards {
		x := pad + int64(c.Section)*(width+int64(k.p.SectionGap)) + inset
		rect, err := kanbanRect(x, pad+cursor[c.Section], k.cardWidth, int64(c.Height))
		if err != nil {
			return KanbanLayout{}, err
		}
		out.Cards[i] = rect
		cursor[c.Section] += int64(c.Height) + int64(k.p.CardGap)
	}
	right, bottom := pad, pad
	for s, section := range k.in.Sections {
		x := pad + int64(s)*(width+int64(k.p.SectionGap))
		extent := cursor[s] - k.band - int64(k.p.CardGap) + geom.FloorDiv(int64(k.p.Gutter), 2)
		height := max(extent+3*int64(k.p.Gutter), int64(k.p.SectionMinHeight)) + k.band - int64(k.p.LabelBandMin)
		frame, err := kanbanRect(x, pad, width, height)
		if err != nil {
			return KanbanLayout{}, err
		}
		labelY := pad + int64(k.p.Border) + geom.FloorDiv(k.band-int64(k.p.Border)-int64(section.LabelHeight), 2)
		label, err := kanbanRect(x, labelY, width, int64(section.LabelHeight))
		if err != nil {
			return KanbanLayout{}, err
		}
		out.Sections[s], out.Labels[s] = frame, label
		right, bottom = max(right, x+width), max(bottom, pad+height)
	}
	canvasW, err := within(right + pad)
	if err != nil {
		return KanbanLayout{}, err
	}
	canvasH, err := within(bottom + pad)
	if err != nil {
		return KanbanLayout{}, err
	}
	out.Canvas = geom.Size{W: int32(canvasW), H: int32(canvasH)}
	return out, nil
}

func kanbanRect(x, y, w, h int64) (geom.Rect, error) {
	right, err := within(x + w)
	if err != nil {
		return geom.Rect{}, err
	}
	bottom, err := within(y + h)
	if err != nil {
		return geom.Rect{}, err
	}
	return geom.Rect{X: int32(x), Y: int32(y), W: int32(right - x), H: int32(bottom - y)}, nil
}
