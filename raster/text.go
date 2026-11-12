package raster

import (
	"embed"
	"image"
	"image/color"
	"sort"
	"sync"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
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

func glyph(f scenelink.Font, cp rune) scenelink.Glyph {
	i := sort.Search(len(f.Glyphs), func(i int) bool { return f.Glyphs[i].Rune >= cp })
	if i < len(f.Glyphs) && f.Glyphs[i].Rune == cp {
		return f.Glyphs[i]
	}
	return scenelink.Glyph{Rune: cp, Advance: fallbackAdvance(f.UnitsPerEm, cp)}
}

func fallbackAdvance(upem int32, cp rune) int32 {
	i := sort.Search(len(gen.UnicodeWidth), func(i int) bool { return gen.UnicodeWidth[i].Hi >= uint32(cp) })
	if i < len(gen.UnicodeWidth) && gen.UnicodeWidth[i].Lo <= uint32(cp) && gen.UnicodeWidth[i].Value == 2 {
		return upem
	}
	return (6*upem + 5) / 10
}

func runFont(t *scene.Text, run scene.Run) int {
	if run.Bold {
		return 1
	}
	if run.Italic || t.Role == scene.TextRoleBody {
		return 0
	}
	return 1
}

func lineWidth(t *scene.Text, line []scene.Run, data scenelink.Outlines) int64 {
	var total int64
	for _, run := range line {
		f := data[runFont(t, run)]
		var sum int64
		for _, cp := range run.Text {
			sum += int64(glyph(f, cp).Advance)
		}
		total += (sum*int64(t.Size)*64 + int64(f.UnitsPerEm) - 1) / int64(f.UnitsPerEm)
	}
	return total
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
	lh := int64(1280)
	if t.Role == scene.TextRoleTitle {
		lh = 1536
	}
	for k, line := range t.Lines {
		x := textLeft(t, lineWidth(t, line, data))
		y := int64(t.Rect.Y) + int64(k)*lh + lh/2 + int64(t.Size)*64*35/100
		z := vector.NewRasterizer(r.image.Bounds().Dx(), r.image.Bounds().Dy())
		r.drawLine(z, t, line, data, x, y)
		z.Draw(r.image, r.image.Bounds(), image.NewUniform(ink), image.Point{})
	}
	return nil
}

func textLeft(t *scene.Text, w int64) int64 {
	x := int64(t.Rect.X)
	switch t.Align {
	case scene.AlignMiddle:
		return x + int64(t.Rect.W)/2 - w/2
	case scene.AlignEnd:
		return x + int64(t.Rect.W) - w
	default:
		return x
	}
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

func (r *renderer) drawLine(z *vector.Rasterizer, t *scene.Text, line []scene.Run, data scenelink.Outlines, x, y int64) {
	for _, run := range line {
		f := data[runFont(t, run)]
		var prefix int64
		for _, cp := range run.Text {
			g := glyph(f, cp)
			origin := x + rounded(prefix*int64(t.Size)*64, int64(f.UnitsPerEm))
			r.drawGlyph(z, g, glyphPlacement{upem: f.UnitsPerEm, size: t.Size, x: origin, y: y, run: run})
			prefix += int64(g.Advance)
		}
		x += rounded(prefix*int64(t.Size)*64, int64(f.UnitsPerEm))
	}
}

func rounded(a, b int64) int64 { return geom.FloorDiv(2*a+b, 2*b) }

type glyphPlacement struct {
	upem, size int32
	x, y       int64
	run        scene.Run
}

func (r *renderer) drawGlyph(z *vector.Rasterizer, g scenelink.Glyph, at glyphPlacement) {
	for _, c := range g.Commands {
		var ps [3]point
		for i, p := range c.Points {
			h := rounded(int64(p[1])*int64(at.size)*64, int64(at.upem))
			px := at.x + rounded(int64(p[0])*int64(at.size)*64, int64(at.upem))
			if at.run.Italic {
				px += geom.FloorDiv(13*h, 64)
			}
			ps[i] = point{float64(px) * r.scale, float64(at.y-h) * r.scale}
		}
		glyphCommand(z, c.Op, ps)
	}
	z.ClosePath()
}

func glyphCommand(z *vector.Rasterizer, op uint8, p [3]point) {
	switch sfnt.SegmentOp(op) {
	case sfnt.SegmentOpMoveTo:
		z.ClosePath()
		z.MoveTo(float32(p[0].x), float32(p[0].y))
	case sfnt.SegmentOpLineTo:
		z.LineTo(float32(p[0].x), float32(p[0].y))
	case sfnt.SegmentOpQuadTo:
		z.QuadTo(float32(p[0].x), float32(p[0].y), float32(p[1].x), float32(p[1].y))
	case sfnt.SegmentOpCubeTo:
		z.CubeTo(float32(p[0].x), float32(p[0].y), float32(p[1].x), float32(p[1].y), float32(p[2].x), float32(p[2].y))
	}
}
