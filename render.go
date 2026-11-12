package mermaid

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"math"

	"github.com/gosuda/elegant-mermaid/internal/cells"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/svg"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

type Scene struct{ value scene.Scene }

func (s *Scene) Dump() []byte { return s.value.AppendJSON(nil) }

func Layout(ctx context.Context, d *Document, o LayoutOptions) (*Scene, error) {
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	if d == nil || d.HasErrors() {
		return nil, fmt.Errorf("%w: document has errors", ErrInvalidDocument)
	}
	options, err := layoutOptions(o)
	if err != nil {
		return nil, err
	}
	in, err := documentLayoutInput(d, options)
	if err != nil {
		return nil, err
	}
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	value, _, err := layout.Layout(in)
	if cancelled := ctx.Err(); cancelled != nil {
		return nil, cancelled
	}
	if err != nil {
		return nil, renderError(err)
	}
	return &Scene{value: value}, nil
}

func documentLayoutInput(d *Document, options scene.Options) (layout.Input, error) {
	if d.diagram == nil || !d.diagram.Supported() {
		return layout.Input{}, fmt.Errorf("%w: parser and layout for %s are not implemented", ErrInvalidDocument, d.kind.String())
	}
	in, err := d.diagram.Input(options.Profile, options)
	if err != nil {
		return layout.Input{}, renderError(err)
	}
	return in, nil
}
func layoutOptions(o LayoutOptions) (scene.Options, error) {
	if o.Profile > ProfileCell || o.Thoroughness < 0 || o.Thoroughness > 5 || o.MaxWidth < 0 || int64(o.MaxWidth) > math.MaxInt32 {
		return scene.Options{}, fmt.Errorf("%w: invalid layout option", ErrBadConfig)
	}
	if err := validateModelLimits(o.Limits); err != nil {
		return scene.Options{}, err
	}
	if _, err := theme.Resolve(o.Theme); err != nil {
		return scene.Options{}, fmt.Errorf("%w: %v", ErrBadConfig, err)
	}
	if len(o.IconPacks) != 0 {
		return scene.Options{}, fmt.Errorf("%w: icon packs are not supported", ErrBadConfig)
	}
	if err := validateLayoutConfig(o.Config); err != nil {
		return scene.Options{}, err
	}
	return scene.Options{Profile: scene.Profile(o.Profile), Thoroughness: int32(o.Thoroughness), MaxWidth: int32(o.MaxWidth), Limits: scene.Limits{MaxNodes: int32(o.Limits.MaxNodes), MaxEdges: int32(o.Limits.MaxEdges), MaxTextBytes: int32(o.Limits.MaxTextBytes)}}, nil
}

func validateModelLimits(l Limits) error {
	for _, v := range []int{l.MaxNodes, l.MaxEdges, l.MaxTextBytes} {
		if v < 0 || int64(v) > math.MaxInt32 {
			return fmt.Errorf("%w: invalid model limit", ErrBadConfig)
		}
	}
	return nil
}

func validateLayoutConfig(config []byte) error {
	if len(bytes.TrimSpace(config)) == 0 {
		return nil
	}
	value, ds := syntax.ParseConfigYAML(config, 0, len(config))
	if len(ds) != 0 || value.Kind != syntax.ValueMapping {
		return fmt.Errorf("%w: config must be a valid mapping", ErrBadConfig)
	}
	return nil
}
func renderError(err error) error {
	sentinel := ErrBadConfig
	if errors.Is(err, layered.ErrTooLarge) {
		sentinel = ErrTooLarge
	} else if errors.Is(err, geom.ErrOverflow) {
		sentinel = ErrOverflow
	}
	return fmt.Errorf("%w: %v", sentinel, err)
}
func RenderSVG(ctx context.Context, d *Document, o SVGOptions) ([]byte, error) {
	o.Profile = ProfileVector
	s, err := Layout(ctx, d, o.LayoutOptions)
	if err != nil {
		return nil, err
	}
	var out bytes.Buffer
	opts := svg.Options{Theme: o.Theme, Background: o.Background, Text: svg.TextMode(o.Text), IDPrefix: o.IDPrefix, Kind: d.kind.String(), Title: d.diagram.AccTitle, Description: d.diagram.AccDescr}
	err = svg.Write(&out, s.value, opts)
	if cancelled := ctx.Err(); cancelled != nil {
		return nil, cancelled
	}
	if err != nil {
		return nil, renderError(err)
	}
	return out.Bytes(), nil
}
func RenderSVGSource(ctx context.Context, src []byte, o SVGOptions) ([]byte, error) {
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	return RenderSVG(ctx, Parse(src), o)
}
func RenderText(ctx context.Context, d *Document, o TextOptions) ([]byte, error) {
	o.Profile = ProfileCell
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	if d == nil || d.HasErrors() {
		return nil, fmt.Errorf("%w: document has errors", ErrInvalidDocument)
	}
	if o.Charset > CharsetASCII || o.Color > ColorTruecolor {
		return nil, fmt.Errorf("%w: invalid text option", ErrBadConfig)
	}
	s, err := Layout(ctx, d, o.LayoutOptions)
	if err != nil {
		return nil, err
	}
	result, err := cells.Render(s.value, cells.Options{Charset: cells.Charset(o.Charset), Color: cells.ColorMode(o.Color), Theme: o.Theme})
	if cancelled := ctx.Err(); cancelled != nil {
		return nil, cancelled
	}
	if err != nil {
		return nil, renderError(err)
	}
	return result.Text, nil
}
func RenderTextSource(ctx context.Context, src []byte, o TextOptions) ([]byte, error) {
	if err := ctx.Err(); err != nil {
		return nil, err
	}
	return RenderText(ctx, Parse(src), o)
}
