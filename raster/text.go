package raster

import (
	"embed"
	"image"
	"image/color"
	"sync"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
	"github.com/gosuda/elegant-mermaid/internal/theme"
	"golang.org/x/image/font"
	"golang.org/x/image/font/sfnt"
	"golang.org/x/image/math/fixed"
	"golang.org/x/image/vector"
)

//go:embed fonts/*.ttf
var fonts embed.FS

var embeddedOutlines = sync.OnceValues(loadOutlines)

func InterOutlines() *mermaid.GlyphOutlines {
	data, err := embeddedOutlines()
	if err != nil {
		return nil
	}
	value, ok := scenelink.NewOutlines(data).(*mermaid.GlyphOutlines)
	if !ok {
		return nil
	}
	return value
}

func loadOutlines() (scenelink.Outlines, error) {
	var out scenelink.Outlines
	names := [2]string{"fonts/Inter-Regular.ttf", "fonts/Inter-SemiBold.ttf"}
	for i, name := range names {
		data, err := fonts.ReadFile(name)
		if err != nil {
			return out, err
		}
		out[i], err = loadFont(data, uint8(i))
		if err != nil {
			return out, err
		}
	}
	return out, nil
}

func loadFont(data []byte, weight uint8) (scenelink.Font, error) {
	f, err := sfnt.Parse(data)
	if err != nil {
		return scenelink.Font{}, err
	}
	out := scenelink.Font{UnitsPerEm: int32(f.UnitsPerEm())}
	var buffer sfnt.Buffer
	for _, row := range gen.Advances {
		if row.Weight != weight {
			continue
		}
		g, err := loadGlyph(f, &buffer, rune(row.CP), out.UnitsPerEm)
		if err != nil {
			return out, err
		}
		out.Glyphs = append(out.Glyphs, g)
	}
	return out, nil
}

func loadGlyph(f *sfnt.Font, b *sfnt.Buffer, cp rune, upem int32) (scenelink.Glyph, error) {
	index, err := f.GlyphIndex(b, cp)
	if err != nil {
		return scenelink.Glyph{}, err
	}
	advance, err := f.GlyphAdvance(b, index, fixed.Int26_6(upem), font.HintingNone)
	if err != nil {
		return scenelink.Glyph{}, err
	}
	segments, err := f.LoadGlyph(b, index, fixed.Int26_6(upem), nil)
	if err != nil {
		return scenelink.Glyph{}, err
	}
	g := scenelink.Glyph{Rune: cp, Advance: int32(advance)}
	for _, s := range segments {
		c := scenelink.Command{Op: uint8(s.Op)}
		for i, p := range s.Args {
			c.Points[i] = [2]int32{int32(p.X), -int32(p.Y)}
		}
		g.Commands = append(g.Commands, c)
	}
	return g, nil
}

func (r *renderer) text(t *scene.Text) error {
	data, err := embeddedOutlines()
	if err != nil {
		return badConfig(err.Error())
	}
	ink, err := r.textPaint(t)
	if err != nil {
		return err
	}
	for k, line := range t.Lines {
		x := scenelink.TextLeft(t, data.LineWidth(t, line))
		z := vector.NewRasterizer(r.image.Bounds().Dx(), r.image.Bounds().Dy())
		for g, at := range data.Glyphs(t, line, x, scenelink.Baseline(t, k)) {
			r.drawGlyph(z, g, at)
		}
		z.Draw(r.image, r.image.Bounds(), image.NewUniform(ink), image.Point{})
	}
	return nil
}

func (r *renderer) textPaint(t *scene.Text) (color.NRGBA, error) {
	row, err := style(t.Style)
	if err != nil {
		return color.NRGBA{}, err
	}
	name := row.Fill
	if name == "on-series" {
		name = "fg"
		if r.theme.SeriesText(t.Series) == theme.TextBackground {
			name = "bg"
		}
	}
	return r.fillPaint(name, t.Series, 255)
}

func (r *renderer) drawGlyph(z *vector.Rasterizer, g scenelink.Glyph, at scenelink.Placement) {
	for _, c := range g.Commands {
		var ps [3]point
		for i, p := range c.Points {
			x, y := at.Point(p[0], p[1])
			ps[i] = point{float64(x) * r.scale, float64(y) * r.scale}
		}
		glyphCommand(z, c.Op, ps)
	}
	z.ClosePath()
}

func glyphCommand(z *vector.Rasterizer, op uint8, p [3]point) {
	switch op {
	case scenelink.OpMoveTo:
		z.ClosePath()
		z.MoveTo(float32(p[0].x), float32(p[0].y))
	case scenelink.OpLineTo:
		z.LineTo(float32(p[0].x), float32(p[0].y))
	case scenelink.OpQuadTo:
		z.QuadTo(float32(p[0].x), float32(p[0].y), float32(p[1].x), float32(p[1].y))
	case scenelink.OpCubeTo:
		z.CubeTo(float32(p[0].x), float32(p[0].y), float32(p[1].x), float32(p[1].y), float32(p[2].x), float32(p[2].y))
	}
}
