package diag

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func AppendSARIF(dst []byte, version string, files []FileDiagnostics) []byte {
	ordered := orderedFiles(files)
	dst = append(dst, `{"$schema":"https://json.schemastore.org/sarif-2.1.0.json","version":"2.1.0","runs":[{"tool":{"driver":{"name":"emd","version":`...)
	dst = AppendString(dst, version)
	dst = append(dst, `,"rules":`...)
	dst = appendRules(dst, ordered)
	dst = append(dst, `}},"results":[`...)
	dst = appendResults(dst, ordered)
	return append(dst, "]}]}\n"...)
}

func appendResults(dst []byte, files []FileDiagnostics) []byte {
	first := true
	for i := range files {
		f := &files[i]
		ix := source.NewIndex(f.Source)
		for j := range f.Diagnostics {
			if !first {
				dst = append(dst, ',')
			}
			first = false
			dst = appendResult(dst, ix, f.Path, &f.Diagnostics[j])
		}
	}
	return dst
}

func appendResult(dst []byte, ix *source.Index, path string, d *Diagnostic) []byte {
	dst = append(dst, `{"ruleId":`...)
	dst = AppendString(dst, d.Code)
	dst = append(dst, `,"level":`...)
	dst = AppendString(dst, sarifLevel(d.Severity))
	dst = append(dst, `,"message":{"text":`...)
	dst = AppendString(dst, d.Message)
	dst = append(dst, `},"locations":[`...)
	dst = appendLocation(dst, ix, path, d.Span)
	dst = append(dst, ']')
	if len(d.Related) > 0 {
		dst = append(dst, `,"relatedLocations":[`...)
		for i := range d.Related {
			if i > 0 {
				dst = append(dst, ',')
			}
			dst = appendRelatedLocation(dst, ix, path, &d.Related[i])
		}
		dst = append(dst, ']')
	}
	return append(dst, '}')
}

func appendLocation(dst []byte, ix *source.Index, path string, sp source.Span) []byte {
	dst = append(dst, `{"physicalLocation":`...)
	dst = appendPhysicalLocation(dst, ix, path, sp)
	return append(dst, '}')
}

func appendPhysicalLocation(dst []byte, ix *source.Index, path string, sp source.Span) []byte {
	dst = append(dst, `{"artifactLocation":{"uri":`...)
	dst = AppendString(dst, path)
	dst = append(dst, `},"region":`...)
	dst = appendRegion(dst, ix, sp)
	return append(dst, '}')
}

func appendRelatedLocation(dst []byte, ix *source.Index, path string, r *Related) []byte {
	dst = append(dst, `{"physicalLocation":`...)
	dst = appendPhysicalLocation(dst, ix, path, r.Span)
	dst = append(dst, `,"message":{"text":`...)
	dst = AppendString(dst, r.Message)
	return append(dst, `}}`...)
}

func appendRegion(dst []byte, ix *source.Index, sp source.Span) []byte {
	start := ix.Position(sp.Start)
	end := ix.Position(sp.End)
	dst = append(dst, `{"startLine":`...)
	dst = strconv.AppendInt(dst, int64(start.Line), 10)
	dst = append(dst, `,"startColumn":`...)
	dst = strconv.AppendInt(dst, int64(ix.UTF16Column(sp.Start)), 10)
	dst = append(dst, `,"endLine":`...)
	dst = strconv.AppendInt(dst, int64(end.Line), 10)
	dst = append(dst, `,"endColumn":`...)
	dst = strconv.AppendInt(dst, int64(ix.UTF16Column(sp.End)), 10)
	return append(dst, '}')
}

func sarifLevel(s Severity) string {
	switch s {
	case SeverityError:
		return "error"
	case SeverityWarning:
		return "warning"
	}
	return "note"
}

func appendRules(dst []byte, files []FileDiagnostics) []byte {
	texts := ruleTexts()
	codes := orderedRuleCodes(resultCodes(files))
	dst = append(dst, '[')
	for i, code := range codes {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = appendRule(dst, code, texts[code])
	}
	return append(dst, ']')
}

func appendRule(dst []byte, code string, t ruleText) []byte {
	dst = append(dst, `{"id":`...)
	dst = AppendString(dst, code)
	dst = append(dst, `,"shortDescription":{"text":`...)
	dst = AppendString(dst, t.summary)
	dst = append(dst, `},"help":{"text":`...)
	dst = AppendString(dst, t.help)
	return append(dst, `}}`...)
}

type ruleText struct {
	summary string
	help    string
}

func ruleTexts() map[string]ruleText {
	texts := make(map[string]ruleText, len(gen.LintRules)+len(gen.Diagnostics))
	for i := range gen.LintRules {
		r := &gen.LintRules[i]
		texts[r.Code] = ruleText{summary: r.Summary, help: r.Help}
	}
	for i := range gen.Diagnostics {
		d := &gen.Diagnostics[i]
		if _, ok := texts[d.Code]; !ok {
			texts[d.Code] = ruleText{summary: d.Summary, help: d.Help}
		}
	}
	return texts
}

func resultCodes(files []FileDiagnostics) []string {
	codes := make([]string, 0, len(files))
	for i := range files {
		for j := range files[i].Diagnostics {
			codes = append(codes, files[i].Diagnostics[j].Code)
		}
	}
	return codes
}

func orderedRuleCodes(codes []string) []string {
	present := make(map[string]bool, len(codes))
	for _, code := range codes {
		present[code] = true
	}
	out := make([]string, 0, len(present))
	out = appendRegistryCodes(out, present)
	for _, code := range codes {
		if present[code] {
			delete(present, code)
			out = append(out, code)
		}
	}
	return out
}

func appendRegistryCodes(out []string, present map[string]bool) []string {
	for i := range gen.LintRules {
		out = takeCode(out, present, gen.LintRules[i].Code)
	}
	for i := range gen.Diagnostics {
		out = takeCode(out, present, gen.Diagnostics[i].Code)
	}
	return out
}

func takeCode(out []string, present map[string]bool, code string) []string {
	if !present[code] {
		return out
	}
	delete(present, code)
	return append(out, code)
}
