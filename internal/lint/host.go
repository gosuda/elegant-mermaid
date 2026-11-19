package lint

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/markdown"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Report struct {
	Source      []byte
	Diagnostics []diag.Diagnostic
}

func LintSource(src []byte, cfg Config) Report {
	a := Analyze(src)
	return Report{Source: a.Source, Diagnostics: Run(a, cfg).All()}
}

func LintHost(host []byte, cfg Config) Report {
	text, bad := source.RepairUTF8(host)
	blocks := markdown.Blocks(text)
	fileDirs, fileFinds := parseFileDirectives(text, append(fencedSpans(text), blockSpans(blocks)...))
	scope := NewFileScope(fileDirs)
	var out []diag.Diagnostic
	if bad >= 0 {
		out = append(out, invalidUTF8(bad))
	}
	for _, b := range blocks {
		a := Analyze(b.Source)
		a.Block.HostOffset = b.HostOffset(0)
		for _, d := range RunWith(a, cfg, scope).All() {
			out = append(out, hostDiagnostic(text, b, d))
		}
	}
	metas := newMetaSet(cfg.Rules())
	out = append(out, metas.report(fileFinds)...)
	out = append(out, metas.report(unusedFindings(scope.Directives, scope.Used))...)
	diag.Sort(out)
	return Report{Source: text, Diagnostics: out}
}

func blockSpans(blocks []markdown.Block) []source.Span {
	spans := make([]source.Span, len(blocks))
	for i, b := range blocks {
		spans[i] = b.Span
	}
	return spans
}

func invalidUTF8(at int) diag.Diagnostic {
	return diag.Diagnostic{
		Code:     "source/invalid-utf8",
		Severity: diag.SeverityError,
		Message:  "invalid UTF-8 at byte " + strconv.Itoa(at),
		Span:     source.Span{Start: at, End: at + len("\uFFFD")},
		Help:     "Save the source as UTF-8.",
	}
}

func hostDiagnostic(host []byte, b markdown.Block, d diag.Diagnostic) diag.Diagnostic {
	d.Span = hostSpan(b, d.Span)
	d.Related = mapRelated(b, d.Related)
	d.Fixes = mapFixes(host, b, d.Fixes)
	return d
}

func hostSpan(b markdown.Block, span source.Span) source.Span {
	start := b.HostOffset(span.Start)
	return source.Span{Start: start, End: max(start, b.HostOffset(span.End))}
}

func mapRelated(b markdown.Block, related []diag.Related) []diag.Related {
	if related == nil {
		return nil
	}
	out := make([]diag.Related, len(related))
	for i, r := range related {
		out[i] = diag.Related{Span: hostSpan(b, r.Span), Message: r.Message}
	}
	return out
}

func mapFixes(host []byte, b markdown.Block, fixes []diag.Fix) []diag.Fix {
	if fixes == nil {
		return nil
	}
	out := make([]diag.Fix, len(fixes))
	for i, f := range fixes {
		out[i] = diag.Fix{Title: f.Title, Safety: f.Safety, Edits: make([]diag.Edit, len(f.Edits))}
		for j, e := range f.Edits {
			out[i].Edits[j] = hostEdit(host, b, e)
		}
	}
	return out
}

func hostEdit(host []byte, b markdown.Block, e diag.Edit) diag.Edit {
	if span, ok := hostLines(host, b, e); ok {
		return diag.Edit{Span: span}
	}
	return diag.Edit{Span: hostSpan(b, e.Span), NewText: e.NewText}
}

func hostLines(host []byte, b markdown.Block, e diag.Edit) (source.Span, bool) {
	src := b.Source
	start, end := e.Span.Start, e.Span.End
	if e.NewText != "" || start >= end || end > len(src) || !startsLine(src, start) {
		return source.Span{}, false
	}
	width := terminatorBefore(src, end)
	if width == 0 && end != len(src) {
		return source.Span{}, false
	}
	contentEnd := b.HostOffset(end - width)
	return source.Span{
		Start: lineStartOf(host, b.HostOffset(start)),
		End:   contentEnd + terminatorAt(host, contentEnd),
	}, true
}

func startsLine(src []byte, at int) bool {
	return at == 0 || terminatorBefore(src, at) > 0
}

func terminatorBefore(src []byte, at int) int {
	switch {
	case at <= 0 || at > len(src):
		return 0
	case src[at-1] == '\n':
		if at >= 2 && src[at-2] == '\r' {
			return 2
		}
		return 1
	case src[at-1] == '\r' && (at == len(src) || src[at] != '\n'):
		return 1
	}
	return 0
}

func terminatorAt(src []byte, at int) int {
	switch {
	case at >= len(src):
		return 0
	case src[at] == '\r' && at+1 < len(src) && src[at+1] == '\n':
		return 2
	case src[at] == '\n' || src[at] == '\r':
		return 1
	}
	return 0
}

func lineStartOf(host []byte, at int) int {
	for at > 0 && host[at-1] != '\n' && host[at-1] != '\r' {
		at--
	}
	return at
}
