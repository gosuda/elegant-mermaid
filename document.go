package mermaid

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout"
	"github.com/gosuda/elegant-mermaid/internal/markdown"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

// Document is immutable. Its caller must keep the borrowed source unchanged.
type Document struct {
	source        []byte
	index         *source.Index
	kind          Kind
	found         bool
	diagnostics   []Diagnostic
	diagram       *layout.Diagram
	preprocessing syntax.Preprocessed
}

func Parse(src []byte) *Document {
	parsed := layout.ParseDiagram(src)
	d := &Document{source: parsed.Source, index: source.NewIndex(parsed.Source), preprocessing: parsed.Preprocessing, diagram: parsed}
	if parsed.Found {
		for k, id := range kindIDs {
			if id == parsed.Kind {
				d.kind, d.found = Kind(k), true
				break
			}
		}
	}
	d.diagnostics = publicDiagnostics(parsed.Diagnostics)
	return d
}
func (d *Document) Source() []byte            { return d.source }
func (d *Document) Kind() (Kind, bool)        { return d.kind, d.found }
func (d *Document) Diagnostics() []Diagnostic { return cloneDiagnostics(d.diagnostics) }
func (d *Document) HasErrors() bool {
	for _, v := range d.diagnostics {
		if v.Severity == SeverityError {
			return true
		}
	}
	return false
}
func (d *Document) Position(offset int) Position {
	p := d.index.Position(offset)
	return Position{Line: p.Line, Column: p.Column}
}
func publicDiagnostics(ds []diag.Diagnostic) []Diagnostic {
	out := make([]Diagnostic, len(ds))
	for i, v := range ds {
		out[i] = Diagnostic{Code: v.Code, Severity: Severity(v.Severity), Message: v.Message, Span: Span(v.Span), Help: v.Help}
		for _, r := range v.Related {
			out[i].Related = append(out[i].Related, Related{Span: Span(r.Span), Message: r.Message})
		}
		for _, f := range v.Fixes {
			fix := Fix{Title: f.Title, Safety: FixSafety(f.Safety)}
			for _, e := range f.Edits {
				fix.Edits = append(fix.Edits, Edit{Span: Span(e.Span), NewText: e.NewText})
			}
			out[i].Fixes = append(out[i].Fixes, fix)
		}
	}
	return out
}
func cloneDiagnostics(ds []Diagnostic) []Diagnostic {
	out := slices.Clone(ds)
	for i := range out {
		out[i].Related = slices.Clone(out[i].Related)
		out[i].Fixes = slices.Clone(out[i].Fixes)
		for j := range out[i].Fixes {
			out[i].Fixes[j].Edits = slices.Clone(out[i].Fixes[j].Edits)
		}
	}
	return out
}
func MarkdownBlocks(src []byte) []Block {
	blocks := markdown.Blocks(src)
	out := make([]Block, len(blocks))
	for i, b := range blocks {
		out[i] = Block{Source: b.Source, Span: Span(b.Span), Lines: make([]BlockLine, len(b.Lines))}
		for j, line := range b.Lines {
			out[i].Lines[j] = BlockLine(line)
		}
	}
	return out
}
