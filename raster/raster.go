package raster

import (
	"bytes"
	"errors"
	"fmt"
	"image"
	"image/color"
	"image/draw"
	"image/png"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
	"github.com/gosuda/elegant-mermaid/internal/theme"
	"golang.org/x/image/vector"
)

type Options struct {
	Scale      int
	Background string
}

var ErrPixelsTooLarge = errors.New("raster pixels too large")
var ErrEncode = errors.New("raster encoding failed")

type ErrorKind uint8

const (
	PixelsTooLarge ErrorKind = iota
	Encode
	InvalidConfig
)

type RasterError struct {
	Kind          ErrorKind
	Width, Height int64
	Message       string
}

func (e *RasterError) Error() string {
	return fmt.Sprintf("raster: %s (%d by %d)", e.Message, e.Width, e.Height)
}

func (e *RasterError) Unwrap() error {
	switch e.Kind {
	case PixelsTooLarge:
		return ErrPixelsTooLarge
	case Encode:
		return ErrEncode
	default:
		return mermaid.ErrBadConfig
	}
}

func badConfig(message string) error {
	return &RasterError{Kind: InvalidConfig, Message: message}
}

func PNG(s *mermaid.Scene, o Options) ([]byte, error) {
	if s == nil {
		return nil, badConfig("nil scene")
	}
	value, ok := scenelink.Scene(s)
	if !ok {
		return nil, badConfig("invalid scene")
	}
	return encodeScene(value, o)
}

type RGBAOptions struct {
	Options
	Theme string
}

// RGBA renders an owned pixel buffer for terminal compositing.
func RGBA(s *mermaid.Scene, o RGBAOptions) (*image.RGBA, error) {
	if s == nil {
		return nil, badConfig("nil scene")
	}
	value, ok := scenelink.Scene(s)
	if !ok {
		return nil, badConfig("invalid scene")
	}
	return drawScene(value, o)
}
func encodeScene(s scene.Scene, o Options) ([]byte, error) {
	pixels, err := drawScene(s, RGBAOptions{Options: o})
	if err != nil {
		return nil, err
	}
	var out bytes.Buffer
	encoder := png.Encoder{CompressionLevel: png.BestCompression}
	if err := encoder.Encode(&out, pixels); err != nil {
		return nil, &RasterError{Kind: Encode, Message: err.Error()}
	}
	return out.Bytes(), nil
}

func drawScene(s scene.Scene, o RGBAOptions) (*image.RGBA, error) {
	r, err := newRenderer(s, o)
	if err != nil {
		return nil, err
	}
	for _, group := range s.Groups {
		if err := r.group(group); err != nil {
			return nil, err
		}
	}
	return r.image, nil
}

type renderer struct {
	image *image.RGBA
	theme theme.Theme
	scale float64
}

func newRenderer(s scene.Scene, o RGBAOptions) (*renderer, error) {
	if o.Scale == 0 {
		o.Scale = 2
	}
	if o.Scale < 1 || o.Scale > 8 || s.Options.Profile != scene.ProfileVector {
		return nil, badConfig("invalid scale or non-vector profile")
	}
	size, err := pixelSize(s.Canvas, o.Scale)
	if err != nil {
		return nil, err
	}
	t, err := theme.Resolve(o.Theme)
	if err != nil {
		return nil, badConfig(err.Error())
	}
	bg := t.Colour(theme.Background)
	if o.Background != "" {
		bg, err = theme.ParseHex(o.Background)
	}
	if err != nil {
		return nil, badConfig(err.Error())
	}
	r := &renderer{image: image.NewRGBA(image.Rectangle{Max: size}), theme: t, scale: float64(o.Scale) / 64}
	draw.Draw(r.image, r.image.Bounds(), image.NewUniform(rgba(bg, 255)), image.Point{}, draw.Src)
	return r, nil
}

func pixelSize(canvas geom.Size, scale int) (image.Point, error) {
	w, h := (int64(canvas.W)*int64(scale)+63)/64, (int64(canvas.H)*int64(scale)+63)/64
	if w > 16384 || h > 16384 || w*h > 67108864 {
		return image.Point{}, &RasterError{Kind: PixelsTooLarge, Width: w, Height: h, Message: "pixel limit exceeded"}
	}
	if w <= 0 || h <= 0 {
		return image.Point{}, badConfig("empty canvas")
	}
	return image.Pt(int(w), int(h)), nil
}

func rgba(c theme.Colour, alpha uint8) color.NRGBA {
	return color.NRGBA{R: c.R, G: c.G, B: c.B, A: alpha}
}

func (r *renderer) group(g *scene.Group) error {
	if g == nil {
		return badConfig("nil group")
	}
	for _, p := range g.Items {
		if err := r.primitive(p); err != nil {
			return err
		}
	}
	return nil
}

func style(name string) (gen.Style, error) {
	for _, row := range gen.Styles {
		if row.Name == name {
			return row, nil
		}
	}
	return gen.Style{}, badConfig("unknown style " + name)
}

func token(name string, series uint8) (theme.Token, error) {
	if name == "series" {
		return theme.Series0 + theme.Token(series%12), nil
	}
	for t := theme.Background; t <= theme.Success; t++ {
		if t.String() == name {
			return t, nil
		}
	}
	return 0, badConfig("unknown colour " + name)
}

func (r *renderer) fillPaint(name string, series, alpha uint8) (color.NRGBA, error) {
	t, err := token(name, series)
	if err != nil {
		return color.NRGBA{}, err
	}
	return rgba(r.theme.Colour(t), alpha), nil
}

func (r *renderer) strokePaint(name string, series, alpha uint8) (color.NRGBA, error) {
	t, err := token(name, series)
	if err != nil {
		return color.NRGBA{}, err
	}
	return rgba(r.theme.Colour(r.theme.Stroke(t)), alpha), nil
}

func (r *renderer) fill(paths []contour, ink color.NRGBA) {
	z := vector.NewRasterizer(r.image.Bounds().Dx(), r.image.Bounds().Dy())
	for _, path := range paths {
		addContour(z, path.points, r.scale)
	}
	z.Draw(r.image, r.image.Bounds(), image.NewUniform(ink), image.Point{})
}

func addContour(z *vector.Rasterizer, points []point, scale float64) {
	if len(points) == 0 {
		return
	}
	z.MoveTo(float32(points[0].x*scale), float32(points[0].y*scale))
	for _, p := range points[1:] {
		z.LineTo(float32(p.x*scale), float32(p.y*scale))
	}
	z.ClosePath()
}

func constant(name string) int32 {
	for _, row := range gen.LayoutConst {
		if row.Name == "vector."+name {
			return row.Value
		}
	}
	return 0
}
