package tui

import (
	"context"
	"fmt"
	"image"
	"os"
	"path/filepath"
	"strings"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/raster"
)

func markdown(path string) bool {
	switch strings.ToLower(filepath.Ext(path)) {
	case ".md", ".markdown", ".mdx":
		return true
	}
	return false
}

func setSourceBlocks(s *State, src []byte) {
	if !markdown(s.Path) {
		return
	}
	s.Blocks = len(mermaid.MarkdownBlocks(src))
	s.Block = max(1, min(s.Block, s.Blocks))
}

func Render(ctx context.Context, s State, src []byte) State {
	if ctx.Err() != nil {
		return s
	}
	s.Errors = 0
	s.Warnings = 0
	s.Diagnostics = nil
	s.Empty = false
	s.MissingBlocks = false
	host := source.NewIndex(src)
	var block *mermaid.Block
	if markdown(s.Path) {
		blocks := mermaid.MarkdownBlocks(src)
		s.Blocks = len(blocks)
		s.Block = max(1, min(s.Block, s.Blocks))
		if len(blocks) == 0 {
			return missingBlocks(s)
		}
		block = &blocks[s.Block-1]
		src = block.Source
	}
	d := mermaid.Parse(src)
	s.Kind = "unknown"
	if k, ok := d.Kind(); ok {
		s.Kind = k.String()
	}
	unknown := collectDiagnostics(&s, d, host, block)
	if s.Errors > 0 {
		if !s.WatchLost && (unknown || s.FrameRev == 0 && !s.Empty) {
			s.Panel = "diagnostics"
			s.AutoPanel = true
		}
		return s
	}
	return renderFrame(ctx, s, d)
}

func missingBlocks(s State) State {
	s.Kind = "-"
	s.Errors = 0
	s.MissingBlocks = true
	if s.AutoPanel {
		s.Panel = ""
		s.AutoPanel = false
	}
	return s
}

func collectDiagnostics(s *State, d *mermaid.Document, host *source.Index, block *mermaid.Block) bool {
	unknown := false
	for _, diagnostic := range d.Diagnostics() {
		severity := diagnosticSeverity(s, diagnostic.Severity)
		p := d.Position(diagnostic.Span.Start)
		if block != nil {
			position := host.Position(block.HostOffset(diagnostic.Span.Start))
			p.Line = position.Line
			p.Column = position.Column
		}
		s.Diagnostics = append(s.Diagnostics, fmt.Sprintf("%s %s %d:%d %s", severity, diagnostic.Code, p.Line, p.Column, diagnostic.Message))
		s.Empty = s.Empty || diagnostic.Code == "common/empty-source"
		unknown = unknown || diagnostic.Code == "common/unknown-diagram-kind"
	}
	return unknown
}

func diagnosticSeverity(s *State, severity mermaid.Severity) string {
	switch severity {
	case mermaid.SeverityError:
		s.Errors++
		return "error"
	case mermaid.SeverityWarning:
		s.Warnings++
		return "warning"
	}
	return "info"
}

func renderFrame(ctx context.Context, s State, d *mermaid.Document) State {
	opts := mermaid.LayoutOptions{Theme: s.Theme}
	charset := mermaid.CharsetUnicode
	if s.ASCII {
		charset = mermaid.CharsetASCII
	}
	text, err := mermaid.RenderText(ctx, d, mermaid.TextOptions{LayoutOptions: opts, Charset: charset, Color: mermaid.ColorMode(s.Color)})
	if err == nil && s.Mode.Pixel() {
		s.Pixels, err = renderPixels(ctx, d, opts)
	}
	if err != nil {
		return renderFailure(s, err)
	}
	s.ColoredText = strings.Split(strings.TrimSuffix(string(text), "\n"), "\n")
	s.Text = strings.Split(strings.TrimSuffix(stripSGR(string(text)), "\n"), "\n")
	s.ContentH = len(s.Text)
	s.ContentW = 0
	for _, line := range s.Text {
		s.ContentW = max(s.ContentW, len([]rune(line)))
	}
	s.FrameRev = s.Displayed
	s.FitImage()
	if s.AutoPanel {
		s.Panel = ""
		s.AutoPanel = false
	}
	return s
}

func renderPixels(ctx context.Context, d *mermaid.Document, opts mermaid.LayoutOptions) (*image.RGBA, error) {
	scene, err := mermaid.Layout(ctx, d, opts)
	if err != nil {
		return nil, err
	}
	return raster.RGBA(scene, raster.RGBAOptions{Options: raster.Options{Scale: 2}, Theme: opts.Theme})
}

func renderFailure(s State, err error) State {
	s.Errors++
	s.Diagnostics = append(s.Diagnostics, err.Error())
	if s.FrameRev == 0 && !s.WatchLost {
		s.Panel = "diagnostics"
		s.AutoPanel = true
	}
	return s
}

func Read(path string) ([]byte, error) {
	src, err := os.ReadFile(path)
	if err != nil {
		return nil, fmt.Errorf("cannot read %s: %w", path, err)
	}
	return src, nil
}
