package tui

import (
	"bytes"
	"fmt"
	"image"
	"image/color"
	"image/png"
	"io"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

func draw(out io.Writer, s State) error {
	if s.Pixels != nil {
		if _, err := io.WriteString(out, "\x1b_Ga=d,d=A,q=2\x1b\\"); err != nil {
			return err
		}
	}
	if _, err := io.WriteString(out, "\x1b[H"+terminalText(s)); err != nil {
		return err
	}
	if !pixelFrameVisible(s) {
		return nil
	}
	pixels, err := composite(s)
	if err != nil {
		return err
	}
	encoded, err := encodePixels(pixels, s.Mode)
	if err != nil {
		return err
	}
	if _, err = io.WriteString(out, "\x1b[1;1H"); err != nil {
		return err
	}
	_, err = out.Write(encoded)
	return err
}

func pixelFrameVisible(s State) bool {
	return s.Mode.Pixel() && s.Pixels != nil && s.Panel == "" && !s.Empty && !s.MissingBlocks
}

func encodePixels(pixels *image.RGBA, mode termgfx.Mode) ([]byte, error) {
	w, h := pixels.Bounds().Dx(), pixels.Bounds().Dy()
	if mode == termgfx.ModeSixel {
		return termgfx.AppendSixel(nil, pixels.Pix, w, h)
	}
	var buffer bytes.Buffer
	if err := png.Encode(&buffer, pixels); err != nil {
		return nil, err
	}
	if mode == termgfx.ModeKitty {
		return termgfx.AppendKitty(nil, buffer.Bytes()), nil
	}
	return termgfx.AppendITerm(nil, buffer.Bytes(), w, h)
}

func composite(s State) (*image.RGBA, error) {
	sw, sh, w, h := s.Extent()
	if int64(w)*int64(h) > 67108864 {
		return nil, fmt.Errorf("viewer viewport exceeds pixel limit")
	}
	if s.CellW <= 0 || s.CellH <= 0 || s.Width > 16384/s.CellW || s.Height-2 > 16384/s.CellH {
		return nil, fmt.Errorf("viewer viewport exceeds pixel limit")
	}
	t, err := theme.Resolve(s.Theme)
	if err != nil {
		return nil, err
	}
	bg := t.Colour(theme.Background)
	dst := image.NewRGBA(image.Rect(0, 0, w, h))
	x0 := max(0, (w-sw)/2)
	y0 := max(0, (h-sh)/2)
	scaled := image.Rect(0, 0, sw, sh)
	background := color.RGBA{R: bg.R, G: bg.G, B: bg.B, A: 255}
	for y := range h {
		for x := range w {
			point := image.Pt(x-x0+s.OffsetX, y-y0+s.OffsetY)
			dst.SetRGBA(x, y, samplePixel(s, point, scaled, background))
		}
	}
	return dst, nil
}

func samplePixel(s State, point image.Point, scaled image.Rectangle, background color.RGBA) color.RGBA {
	if point.In(scaled) {
		return s.Pixels.RGBAAt(point.X*100/s.Zoom, point.Y*100/s.Zoom)
	}
	return background
}
