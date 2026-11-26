package cli

import (
	"bytes"
	"errors"
	"fmt"

	mermaid "github.com/gosuda/elegant-mermaid"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/markdown"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

type markdownDiagram struct {
	diagram *layout.Diagram
	config  syntax.EffectiveConfig
}

type markdownArtifact struct {
	data  []byte
	title string
}

func resolveMarkdownOptions(o *commandOptions, path string) error {
	if !markdownHost(path) {
		if o.artifactsSet {
			return errors.New("-a requires Markdown input")
		}
		return nil
	}
	if o.output == "" && !o.artifactsSet {
		return errors.New("rendering Markdown input requires -o OUTPUT or -a ARTEFACT_DIR")
	}
	if !markdownHost(o.output) {
		return nil
	}
	if o.format == "" {
		o.format = "svg"
	}
	return validateChoice(o.format, "-e", "svg", "png")
}

// Raw spans own the rewritten bytes. Repaired blocks supply the diagnostic
// coordinates, while parsing raw block text retains invalid-UTF-8 errors.
func renderMarkdown(cfg Config, o commandOptions, path string, raw []byte) error {
	blocks := markdown.Blocks(raw)
	if len(blocks) == 0 {
		return resultError(cfg, fmt.Errorf("no Mermaid blocks found in %s; add a fenced code block labelled mermaid", path))
	}
	repaired, _ := source.RepairUTF8(raw)
	mapped := markdown.Blocks(repaired)
	prepared, diagnostics, err := prepareMarkdownBlocks(path, blocks, mapped, o.site)
	if err != nil {
		return err
	}
	f := diag.FileDiagnostics{Path: path, Source: repaired, Diagnostics: diagnostics}
	if hasErrors(diagnostics) {
		return reportMarkdownDiagnostics(cfg, o, f)
	}
	artifacts, additional, renderErr := encodeMarkdownBlocks(cfg, o, prepared, mapped)
	f.Diagnostics = append(f.Diagnostics, additional...)
	if err = reportMarkdownDiagnostics(cfg, o, f); err != nil {
		return err
	}
	if renderErr != nil {
		if errors.Is(renderErr, mermaid.ErrBadConfig) {
			return renderErr
		}
		return resultError(cfg, renderErr)
	}
	return writeMarkdownOutputs(path, raw, blocks, artifacts, o)
}

func prepareMarkdownBlocks(path string, raw, mapped []markdown.Block, site syntax.ConfigValue) ([]markdownDiagram, []diag.Diagnostic, error) {
	if len(raw) != len(mapped) {
		return nil, nil, markdownBoundaryError(path)
	}
	prepared := make([]markdownDiagram, 0, len(raw))
	var diagnostics []diag.Diagnostic
	for i, block := range raw {
		_, diagram, err := parseInput(path, block.Source)
		if err != nil {
			return nil, nil, err
		}
		if !bytes.Equal(diagram.Source, mapped[i].Source) {
			return nil, nil, markdownBoundaryError(path)
		}
		config, err := diagram.EffectiveConfig(site)
		if err != nil {
			return nil, nil, err
		}
		diagnostics = appendHostDiagnostics(diagnostics, mapped[i], diagram.DiagnosticsFor(config))
		prepared = append(prepared, markdownDiagram{diagram: diagram, config: config})
	}
	return prepared, diagnostics, nil
}

// Every scene is encoded in memory before output directories or files exist.
func encodeMarkdownBlocks(cfg Config, o commandOptions, prepared []markdownDiagram, mapped []markdown.Block) ([]markdownArtifact, []diag.Diagnostic, error) {
	artifacts := make([]markdownArtifact, 0, len(prepared))
	var diagnostics []diag.Diagnostic
	for i, block := range prepared {
		s, additional, err := layoutDiagram(o, block.diagram, block.config)
		diagnostics = appendHostDiagnostics(diagnostics, mapped[i], additional)
		if err != nil {
			return nil, diagnostics, err
		}
		data, err := encodeScene(cfg, o, s, svgOptionsOf(o, block.diagram, block.config))
		if err != nil {
			return nil, diagnostics, err
		}
		artifacts = append(artifacts, markdownArtifact{data: data, title: block.diagram.AccTitle})
	}
	return artifacts, diagnostics, nil
}

func appendHostDiagnostics(dst []diag.Diagnostic, block markdown.Block, diagnostics []diag.Diagnostic) []diag.Diagnostic {
	for _, diagnostic := range diagnostics {
		dst = append(dst, hostDiagnostic(block, diagnostic))
	}
	return dst
}

func reportMarkdownDiagnostics(cfg Config, o commandOptions, f diag.FileDiagnostics) error {
	diag.Sort(f.Diagnostics)
	return rejectInvalidSource(cfg, o, f)
}

func markdownBoundaryError(path string) error {
	return fmt.Errorf("cannot render %s: Markdown block boundaries changed during UTF-8 repair", path)
}
