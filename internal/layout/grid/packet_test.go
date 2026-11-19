package grid

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

func vectorPacketParams() PacketParams {
	return PacketParams{BitsPerRow: 32, BitWidth: 2048, RowHeight: 2048, PaddingX: 320, PaddingY: 320, ShowBitsPad: 1024, MarginX: 64, LineHeight: 1280, ShowBits: true}
}

func cellPacketParams() PacketParams {
	return PacketParams{BitsPerRow: 32, BitWidth: 2, RowHeight: 3, PaddingX: 1, PaddingY: 1, LineHeight: 1, ShowBits: true}
}

func piece(start, end int64, lead, trail int32) PacketPiece {
	return PacketPiece{Start: start, End: end, Lead: geom.Size{W: lead, H: 1}, Trail: geom.Size{W: trail, H: 1}}
}

func TestPacketVectorGeometry(t *testing.T) {
	in := PacketInput{Pieces: []PacketPiece{piece(0, 15, 500, 900), piece(16, 31, 900, 900), piece(32, 32, 500, 0)}, HasTitle: true}
	out, err := Packet(in, vectorPacketParams())
	require.NoError(t, err)
	require.Equal(t, []geom.Rect{
		{X: 64, Y: 1344, W: 32448, H: 2048},
		{X: 32832, Y: 1344, W: 32448, H: 2048},
		{X: 64, Y: 4736, W: 1728, H: 2048},
	}, out.Rects)
	require.Equal(t, geom.Rect{X: 64, Y: 64, W: 500, H: 1280}, out.Lead[0])
	require.Equal(t, geom.Rect{X: 64 + 32448 - 900, Y: 64, W: 900, H: 1280}, out.Trail[0])
	require.Equal(t, geom.Rect{X: 64 + 864 - 250, Y: 3456, W: 500, H: 1280}, out.Lead[2])
	require.Equal(t, geom.Rect{}, out.Trail[2])
	require.Equal(t, geom.Rect{X: 64, Y: 2*3392 + 1344, W: 65536, H: 2048}, out.Title)
	require.Equal(t, geom.Size{W: 65664, H: 2*3392 + 1344 + 2048}, out.Canvas)
	require.Equal(t, 2, out.Rows)
}

func TestPacketCellGeometry(t *testing.T) {
	in := PacketInput{Pieces: []PacketPiece{piece(0, 3, 1, 1), piece(4, 4, 1, 0), piece(106, 106, 3, 0)}}
	out, err := Packet(in, cellPacketParams())
	require.NoError(t, err)
	require.Equal(t, geom.Rect{X: 0, Y: 1, W: 7, H: 3}, out.Rects[0])
	require.Equal(t, geom.Rect{X: 8, Y: 1, W: 1, H: 3}, out.Rects[1])
	require.Equal(t, geom.Rect{X: 20, Y: 13, W: 1, H: 3}, out.Rects[2])
	require.Equal(t, geom.Rect{X: 0, Y: 0, W: 1, H: 1}, out.Lead[0])
	require.Equal(t, geom.Rect{X: 6, Y: 0, W: 1, H: 1}, out.Trail[0])
	require.Equal(t, geom.Rect{X: 19, Y: 12, W: 3, H: 1}, out.Lead[2])
	require.Equal(t, geom.Size{W: 64, H: 17}, out.Canvas)
	require.Equal(t, 4, out.Rows)
}

func TestPacketDescendingMirrorsTheRow(t *testing.T) {
	p := vectorPacketParams()
	p.BitsPerRow, p.Descending = 16, true
	out, err := Packet(PacketInput{Pieces: []PacketPiece{piece(0, 7, 100, 100), piece(8, 11, 100, 100), piece(12, 12, 100, 0), piece(13, 15, 100, 100)}}, p)
	require.NoError(t, err)
	xs := make([]int32, len(out.Rects))
	for i, r := range out.Rects {
		xs[i] = r.X
	}
	require.Equal(t, []int32{64 + 8*2048, 64 + 4*2048, 64 + 3*2048, 64}, xs)
	require.Equal(t, int32(64+16*2048+64), out.Canvas.W)
}

func TestPacketWithoutBitNumbers(t *testing.T) {
	p := vectorPacketParams()
	p.ShowBits = false
	out, err := Packet(PacketInput{Pieces: []PacketPiece{piece(0, 3, 500, 500), piece(32, 33, 500, 500)}}, p)
	require.NoError(t, err)
	require.Equal(t, int32(320), out.Rects[0].Y)
	require.Equal(t, int32(320+2048+320), out.Rects[1].Y)
	require.Equal(t, []geom.Rect{{}, {}}, out.Lead)
	require.Equal(t, []geom.Rect{{}, {}}, out.Trail)
	require.Equal(t, int32(2*(2048+320)+320), out.Canvas.H)
}

func TestPacketEmpty(t *testing.T) {
	out, err := Packet(PacketInput{}, vectorPacketParams())
	require.NoError(t, err)
	require.Equal(t, geom.Size{W: 65664, H: 1344}, out.Canvas)
	titled, err := Packet(PacketInput{HasTitle: true}, vectorPacketParams())
	require.NoError(t, err)
	require.Equal(t, geom.Rect{X: 64, Y: 1344, W: 65536, H: 2048}, titled.Title)
	require.Equal(t, geom.Size{W: 65664, H: 1344 + 2048}, titled.Canvas)
}

func TestPacketNarrowFieldsClampToZeroWidth(t *testing.T) {
	p := vectorPacketParams()
	p.BitWidth, p.PaddingX = 1, 5
	out, err := Packet(PacketInput{Pieces: []PacketPiece{piece(0, 2, 10, 10), piece(3, 8, 10, 10)}}, p)
	require.NoError(t, err)
	require.Equal(t, int32(0), out.Rects[0].W)
	require.Equal(t, int32(1), out.Rects[1].W)
}

func TestPacketLabelBandNeverExceedsThePadding(t *testing.T) {
	p := vectorPacketParams()
	p.PaddingY, p.ShowBitsPad = 0, 640
	out, err := Packet(PacketInput{Pieces: []PacketPiece{piece(0, 3, 100, 100)}}, p)
	require.NoError(t, err)
	require.Equal(t, geom.Rect{X: 64, Y: 0, W: 100, H: 640}, out.Lead[0])
	require.Equal(t, int32(640), out.Rects[0].Y)
}

func TestPacketLabelsNeverStartLeftOfTheCanvas(t *testing.T) {
	out, err := Packet(PacketInput{Pieces: []PacketPiece{piece(64, 64, 3, 0), piece(65, 65, 3, 0)}}, cellPacketParams())
	require.NoError(t, err)
	require.Equal(t, int32(0), out.Lead[0].X)
	require.Equal(t, int32(1), out.Lead[1].X)
}

func TestPacketRejectsInvalidInput(t *testing.T) {
	good := vectorPacketParams()
	for name, tc := range map[string]struct {
		in PacketInput
		p  func(*PacketParams)
	}{
		"crosses a row":    {PacketInput{Pieces: []PacketPiece{piece(30, 33, 1, 1)}}, nil},
		"reversed":         {PacketInput{Pieces: []PacketPiece{piece(4, 3, 1, 1)}}, nil},
		"negative start":   {PacketInput{Pieces: []PacketPiece{piece(-1, 3, 1, 1)}}, nil},
		"negative label":   {PacketInput{Pieces: []PacketPiece{{Start: 0, End: 1, Lead: geom.Size{W: -1}}}}, nil},
		"zero bits":        {PacketInput{}, func(p *PacketParams) { p.BitsPerRow = 0 }},
		"zero bit width":   {PacketInput{}, func(p *PacketParams) { p.BitWidth = 0 }},
		"zero row height":  {PacketInput{}, func(p *PacketParams) { p.RowHeight = 0 }},
		"negative padding": {PacketInput{}, func(p *PacketParams) { p.PaddingX = -1 }},
		"negative margin":  {PacketInput{}, func(p *PacketParams) { p.MarginX = -1 }},
	} {
		p := good
		if tc.p != nil {
			tc.p(&p)
		}
		_, err := Packet(tc.in, p)
		require.ErrorIs(t, err, geom.ErrDomain, name)
	}
}

func TestPacketOverflow(t *testing.T) {
	p := vectorPacketParams()
	p.RowHeight, p.PaddingY = 1<<28, 1<<28
	_, err := Packet(PacketInput{Pieces: []PacketPiece{piece(32, 32, 1, 0)}}, p)
	require.ErrorIs(t, err, geom.ErrOverflow)
	wide := vectorPacketParams()
	wide.BitsPerRow, wide.BitWidth = 1<<20, 1<<20
	_, err = Packet(PacketInput{}, wide)
	require.ErrorIs(t, err, geom.ErrOverflow)
	_, err = Packet(PacketInput{Pieces: []PacketPiece{piece(1<<40, 1<<40, 1, 0)}}, vectorPacketParams())
	require.ErrorIs(t, err, geom.ErrOverflow)
}

func TestPacketRowsAreContiguousAndDisjoint(t *testing.T) {
	var pieces []PacketPiece
	for start := int64(0); start < 200; {
		end := min(start+int64(start%7), 199, (start/32+1)*32-1)
		pieces = append(pieces, piece(start, end, 40, 40))
		start = end + 1
	}
	for _, p := range []PacketParams{vectorPacketParams(), cellPacketParams()} {
		out, err := Packet(PacketInput{Pieces: pieces, HasTitle: true}, p)
		require.NoError(t, err)
		for i, a := range out.Rects {
			require.GreaterOrEqual(t, a.X, p.MarginX)
			require.LessOrEqual(t, a.X+a.W, out.Canvas.W-p.MarginX)
			require.LessOrEqual(t, a.Y+a.H, out.Title.Y)
			for j := i + 1; j < len(out.Rects); j++ {
				overlap, err := geom.Intersects(a, out.Rects[j])
				require.NoError(t, err)
				require.False(t, overlap, "%d %d", i, j)
			}
			for _, label := range []geom.Rect{out.Lead[i], out.Trail[i]} {
				for j, b := range out.Rects {
					overlap, err := geom.Intersects(label, b)
					require.NoError(t, err)
					require.False(t, overlap, "label %d box %d", i, j)
				}
			}
		}
	}
}
