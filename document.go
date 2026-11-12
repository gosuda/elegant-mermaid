package mermaid

import (
	"fmt"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/markdown"
	model "github.com/gosuda/elegant-mermaid/internal/model/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	parser "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

// Document is immutable. Its caller must keep the borrowed source unchanged.
type Document struct {
	source        []byte
	index         *source.Index
	kind          Kind
	found         bool
	diagnostics   []Diagnostic
	model         *model.Model
	preprocessing syntax.Preprocessed
}

func Parse(src []byte) *Document {
	text, bad := source.RepairUTF8(src)
	p := syntax.Preprocess(text)
	detected := syntax.Detect(text, p.Removed)
	d := &Document{source: text, index: source.NewIndex(text), preprocessing: p}
	ds := append(p.Diags, detected.Diagnostics...)
	if bad >= 0 {
		ds = append(ds, diag.Diagnostic{Code: "source/invalid-utf8", Severity: diag.SeverityError, Message: fmt.Sprintf("invalid UTF-8 at byte %d", bad), Span: source.Span{Start: bad, End: bad + 3}, Help: "Save the source as UTF-8."})
	}
	if detected.Found {
		for k, id := range kindIDs {
			if id == detected.Kind {
				d.kind, d.found = Kind(k), true
				break
			}
		}
		if detected.Kind == "flowchart" {
			ast, syntaxDiagnostics := parser.Parse(text, p.Removed)
			ds = append(ds, syntaxDiagnostics...)
			var semanticDiagnostics []diag.Diagnostic
			d.model, semanticDiagnostics = model.Resolve(text, ast)
			ds = append(ds, semanticDiagnostics...)
		}
	}
	diag.Sort(ds)
	d.diagnostics = publicDiagnostics(ds)
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
