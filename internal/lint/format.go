package lint

import (
	"bytes"
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
)

type Format uint8

const (
	FormatText Format = iota
	FormatJSON
	FormatSARIF
	FormatGitHub
)

var formatNames = [...]string{"text", "json", "sarif", "github"}

func (f Format) String() string {
	if int(f) < len(formatNames) {
		return formatNames[f]
	}
	return "text"
}

func ParseFormat(name string) (Format, bool) {
	i := slices.Index(formatNames[:], name)
	return Format(max(i, 0)), i >= 0
}

type RenderOptions struct {
	Version string
	Colour  bool
	Width   func(r rune) int
}

func Render(f Format, files []diag.FileDiagnostics, o RenderOptions) ([]byte, error) {
	switch f {
	case FormatJSON:
		return diag.AppendDocument(nil, files), nil
	case FormatSARIF:
		return diag.AppendSARIF(nil, o.Version, files), nil
	case FormatGitHub:
		return diag.AppendGitHub(nil, files), nil
	}
	return renderText(files, o)
}

func orderedFiles(files []diag.FileDiagnostics) []diag.FileDiagnostics {
	out := slices.Clone(files)
	for i := range out {
		out[i].Diagnostics = slices.Clone(out[i].Diagnostics)
		diag.Sort(out[i].Diagnostics)
	}
	slices.SortStableFunc(out, func(a, b diag.FileDiagnostics) int {
		return strings.Compare(a.Path, b.Path)
	})
	return out
}

func renderText(files []diag.FileDiagnostics, o RenderOptions) ([]byte, error) {
	var out bytes.Buffer
	frame := diag.RenderText
	if o.Colour {
		frame = diag.RenderTextColour
	}
	for _, f := range orderedFiles(files) {
		if len(f.Diagnostics) == 0 {
			continue
		}
		if out.Len() > 0 {
			out.WriteByte('\n')
		}
		if err := frame(&out, f.Path, f.Source, f.Diagnostics, diag.FrameOptions{Width: o.Width}); err != nil {
			return nil, err
		}
	}
	return out.Bytes(), nil
}
