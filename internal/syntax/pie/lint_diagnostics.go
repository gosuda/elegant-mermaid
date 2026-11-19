package pie

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func sliceDiagnostics(src []byte, removed []source.Span, document *Pie) []diag.Diagnostic {
	var out []diag.Diagnostic
	text := string(src)
	for start := 0; start < len(text); {
		end := sliceLineEnd(text, start)
		raw := text[start:end]
		line := strings.TrimSpace(sliceComment(raw))
		at := start + len(raw) - len(strings.TrimLeft(raw, " \t"))
		skip := ignoredSliceLine(line, source.Span{Start: start, End: end}, removed) || metadataSliceLine(document, start, end)
		if !skip {
			out = append(out, pieSyntaxLine(line, at)...)
		}
		start = end + 1
		start = skipSliceLF(text, end, start)
	}
	return out
}

func sliceLineEnd(text string, start int) int {
	end := start
	for end < len(text) && text[end] != '\r' && text[end] != '\n' {
		end++
	}
	return end
}

func skipSliceLF(text string, end, start int) int {
	if end < len(text) && text[end] == '\r' && start < len(text) && text[start] == '\n' {
		return start + 1
	}
	return start
}

func pieSyntaxLine(line string, at int) []diag.Diagnostic {
	emit := func(code string, span source.Span, replacement string) []diag.Diagnostic {
		span.Start += at
		span.End += at
		return sliceIssue(code, span, replacement)
	}
	if line[0] != '"' && line[0] != '\'' {
		return unquotedSliceIssue(line, at)
	}
	quote := line[0]
	beforeColon, _, hasColon := strings.Cut(line, ":")
	close := sliceLabelClose(line, quote)
	if close < 0 {
		end := len(line)
		if hasColon {
			end = len(strings.TrimRight(beforeColon, " \t"))
		}
		return emit("pie/quote-unclosed", source.Span{Start: end, End: end}, string(quote))
	}
	if ds := quotedSliceIssue(line[1:close], quote, at, close); ds != nil {
		return ds
	}
	tail := strings.TrimSpace(line[close+1:])
	number, hasColon := strings.CutPrefix(tail, ":")
	if !hasColon {
		return emit("pie/missing-colon", source.Span{Start: close + 1, End: close + 1}, " :")
	}
	if strings.TrimSpace(number) == "" {
		return emit("pie/missing-number", source.Span{Start: len(line), End: len(line)}, "")
	}
	return nil
}

func unquotedSliceIssue(line string, at int) []diag.Diagnostic {
	label, _, found := strings.Cut(line, ":")
	label = strings.TrimSpace(label)
	if found && label != "" {
		return sliceIssue("pie/label-requires-quotes", source.Span{Start: at, End: at + len(label)}, "\""+label+"\"")
	}
	return nil
}

func quotedSliceIssue(label string, quote byte, at, close int) []diag.Diagnostic {
	if quote != '"' || strings.Contains(label, "\\\"") {
		return nil
	}
	span := source.Span{Start: at + 1, End: at + close}
	if strings.ContainsRune(label, '"') {
		return sliceIssue("pie/label-double-in-double", span, "")
	}
	return nil
}

func sliceLabelClose(line string, quote byte) int {
	first := firstSliceQuote(line, quote)
	if first < 0 {
		return -1
	}
	if strings.HasPrefix(strings.TrimSpace(line[first+1:]), ":") {
		return first
	}
	colon := strings.IndexByte(line[first+1:], ':')
	if colon < 0 {
		return first
	}
	return strings.LastIndexByte(line[:first+1+colon], quote)
}

func firstSliceQuote(line string, quote byte) int {
	escaped := false
	for i := 1; i < len(line); i++ {
		if escaped {
			escaped = false
			continue
		}
		if line[i] == '\\' {
			escaped = true
			continue
		}
		if line[i] == quote {
			return i
		}
	}
	return -1
}

func ignoredSliceLine(line string, span source.Span, removed []source.Span) bool {
	if line == "" || strings.HasPrefix(line, "%%") {
		return true
	}
	for _, r := range removed {
		if r.Start < span.End && r.End > span.Start {
			return true
		}
	}
	for _, prefix := range []string{"pie", "title", "accTitle", "accDescr"} {
		rest, found := strings.CutPrefix(line, prefix)
		if found && (rest == "" || strings.ContainsAny(rest[:1], " \t:")) {
			return true
		}
	}
	return false
}

func sliceIssue(code string, span source.Span, replacement string) []diag.Diagnostic {
	for _, row := range gen.LintRules {
		if row.Code != code {
			continue
		}
		d := diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: row.Summary, Help: row.Help, Span: span}
		if row.FixSafety != "none" {
			safety := diag.FixSafe
			if row.FixSafety == "unsafe" {
				safety = diag.FixUnsafe
			}
			d.Fixes = []diag.Fix{{Title: "Repair pie slice label", Safety: safety, Edits: []diag.Edit{{Span: span, NewText: replacement}}}}
		}
		return []diag.Diagnostic{d}
	}
	return nil
}

func mergeSliceDiagnostics(text string, parsed, specific []diag.Diagnostic) []diag.Diagnostic {
	out := parsed[:0]
	for _, d := range parsed {
		replaced := sliceDiagnosticReplaced(text, d, specific)
		if !replaced {
			out = append(out, d)
		}
	}
	return append(out, specific...)
}

func sliceDiagnosticReplaced(text string, d diag.Diagnostic, specific []diag.Diagnostic) bool {
	for _, s := range specific {
		lo, hi := s.Span.Start, s.Span.End
		for lo > 0 && text[lo-1] != '\n' && text[lo-1] != '\r' {
			lo--
		}
		hi = sliceLineEnd(text, hi)
		if d.Span.Start >= lo && d.Span.Start <= hi {
			return true
		}
	}
	return false
}

func sliceComment(line string) string {
	var quote byte
	escaped := false
	for i := range len(line) {
		c := line[i]
		if escaped {
			escaped = false
			continue
		}
		if quote != 0 {
			quote, escaped = sliceQuoteState(c, quote)
			continue
		}
		if c == '"' || c == '\'' {
			quote = c
			continue
		}
		if c == '%' && i+1 < len(line) && line[i+1] == '%' {
			return line[:i]
		}
	}
	return line
}

func sliceQuoteState(c, quote byte) (byte, bool) {
	switch c {
	case '\\':
		return quote, true
	case quote:
		return 0, false
	default:
		return quote, false
	}
}

func metadataSliceLine(document *Pie, start, end int) bool {
	for _, statement := range document.Body {
		switch item := statement.Kind.(type) {
		case *TitleAndAccessibilities:
			if statement.Span.Start < end && statement.Span.End > start {
				return true
			}
		case *PieSection:
			if multilineSliceLabel(item.Label.Span, start, end) {
				return true
			}
		}
	}
	return false
}

func multilineSliceLabel(span source.Span, start, end int) bool {
	return span.Start < end && span.End > start && (span.Start < start || span.End > end)
}
