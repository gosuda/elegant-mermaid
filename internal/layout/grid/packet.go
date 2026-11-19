package grid

import "github.com/gosuda/elegant-mermaid/internal/geom"

type PacketPiece struct {
	Start, End  int64
	Lead, Trail geom.Size
}

type PacketInput struct {
	Pieces   []PacketPiece
	HasTitle bool
}

type PacketParams struct {
	BitsPerRow  int32
	BitWidth    int32
	RowHeight   int32
	PaddingX    int32
	PaddingY    int32
	ShowBitsPad int32
	MarginX     int32
	LineHeight  int32
	ShowBits    bool
	Descending  bool
}

type PacketLayout struct {
	Rects  []geom.Rect
	Lead   []geom.Rect
	Trail  []geom.Rect
	Title  geom.Rect
	Canvas geom.Size
	Rows   int
}

type packetPlan struct {
	in      PacketInput
	p       PacketParams
	padY    int64
	pitch   int64
	bits    int64
	labelH  int64
	out     PacketLayout
	maxRows int64
	width   int64
}

func (p PacketParams) valid() bool {
	positive := p.BitsPerRow >= 1 && p.BitWidth >= 1 && p.RowHeight >= 1
	return positive && p.PaddingX >= 0 && p.PaddingY >= 0 && p.ShowBitsPad >= 0 && p.MarginX >= 0 && p.LineHeight >= 0
}

func Packet(in PacketInput, p PacketParams) (PacketLayout, error) {
	if !p.valid() {
		return PacketLayout{}, geom.ErrDomain
	}
	b := &packetPlan{in: in, p: p, bits: int64(p.BitsPerRow), padY: int64(p.PaddingY)}
	if p.ShowBits {
		b.padY += int64(p.ShowBitsPad)
	}
	b.pitch = int64(p.RowHeight) + b.padY
	b.labelH = min(int64(p.LineHeight), b.padY)
	width, err := within(b.bits*int64(p.BitWidth) + 2*int64(p.MarginX))
	if err != nil {
		return PacketLayout{}, err
	}
	b.width = width
	b.out = PacketLayout{
		Rects: make([]geom.Rect, len(in.Pieces)),
		Lead:  make([]geom.Rect, len(in.Pieces)),
		Trail: make([]geom.Rect, len(in.Pieces)),
	}
	for i, piece := range in.Pieces {
		if err := b.place(i, piece); err != nil {
			return PacketLayout{}, err
		}
	}
	return b.close()
}

func (piece PacketPiece) valid() bool {
	sizes := piece.Lead.W >= 0 && piece.Lead.H >= 0 && piece.Trail.W >= 0 && piece.Trail.H >= 0
	return sizes && piece.Start >= 0 && piece.End >= piece.Start
}

func (b *packetPlan) locate(piece PacketPiece) (row, column, n int64, err error) {
	if !piece.valid() {
		return 0, 0, 0, geom.ErrDomain
	}
	n = piece.End - piece.Start + 1
	row = geom.FloorDiv(piece.Start, b.bits)
	column = piece.Start - row*b.bits
	if column+n > b.bits {
		return 0, 0, 0, geom.ErrDomain
	}
	if b.p.Descending {
		column = b.bits - column - n
	}
	return row, column, n, nil
}

func (b *packetPlan) place(i int, piece PacketPiece) error {
	row, column, n, err := b.locate(piece)
	if err != nil {
		return err
	}
	offset, err := product(row, b.pitch)
	if err != nil {
		return err
	}
	y, err := within(offset + b.padY)
	if err != nil {
		return err
	}
	x := column*int64(b.p.BitWidth) + int64(b.p.MarginX)
	w := max(n*int64(b.p.BitWidth)-int64(b.p.PaddingX), 0)
	b.maxRows = max(b.maxRows, row+1)
	b.out.Rects[i] = geom.Rect{X: int32(x), Y: int32(y), W: int32(w), H: b.p.RowHeight}
	if b.p.ShowBits {
		b.bitLabels(i, n, x, y, w, piece)
	}
	return nil
}

func (b *packetPlan) bitLabels(i int, n, x, y, w int64, piece PacketPiece) {
	top := int32(y - b.labelH)
	h := int32(b.labelH)
	lead := int64(piece.Lead.W)
	if n == 1 {
		b.out.Lead[i] = geom.Rect{X: int32(max(x+w/2-lead/2, 0)), Y: top, W: piece.Lead.W, H: h}
		return
	}
	trail := int64(piece.Trail.W)
	b.out.Lead[i] = geom.Rect{X: int32(x), Y: top, W: piece.Lead.W, H: h}
	b.out.Trail[i] = geom.Rect{X: int32(max(x+w-trail, 0)), Y: top, W: piece.Trail.W, H: h}
}

func (b *packetPlan) close() (PacketLayout, error) {
	offset, err := product(b.maxRows, b.pitch)
	if err != nil {
		return PacketLayout{}, err
	}
	height, err := within(offset + b.padY + b.titleHeight())
	if err != nil {
		return PacketLayout{}, err
	}
	if b.in.HasTitle {
		b.out.Title = geom.Rect{X: b.p.MarginX, Y: int32(height) - b.p.RowHeight, W: int32(b.bits * int64(b.p.BitWidth)), H: b.p.RowHeight}
	}
	b.out.Canvas = geom.Size{W: int32(b.width), H: int32(height)}
	b.out.Rows = int(b.maxRows)
	return b.out, nil
}

func (b *packetPlan) titleHeight() int64 {
	if b.in.HasTitle {
		return int64(b.p.RowHeight)
	}
	return 0
}
