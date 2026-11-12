package syntax

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnknownKind = "common/unknown-diagram-kind"
	codeEmptySource = "common/empty-source"

	headerTokenPlaceholder = "TOKEN"
)

type Detection struct {
	Kind        string
	Found       bool
	Header      source.Span
	Diagnostics []diag.Diagnostic
}

func Detect(src []byte, removed []source.Span) Detection {
	start, ok := headerStart(src, removed)
	if !ok {
		return Detection{Diagnostics: []diag.Diagnostic{emptySourceDiagnostic()}}
	}
	header := source.Span{Start: start, End: tokenEnd(src, start)}
	token := string(src[header.Start:header.End])
	kind, ok := matchKind(token)
	if !ok {
		return Detection{Header: header, Diagnostics: []diag.Diagnostic{unknownKindDiagnostic(header, token)}}
	}
	return Detection{Kind: kind, Found: true, Header: header}
}

func headerStart(src []byte, removed []source.Span) (int, bool) {
	pos := 0
	next := 0
	for pos < len(src) {
		for next < len(removed) && removed[next].End <= pos {
			next++
		}
		if next < len(removed) && pos >= removed[next].Start {
			pos = removed[next].End
			continue
		}
		if isSkipByte(src[pos]) {
			pos++
			continue
		}
		return pos, true
	}
	return len(src), false
}

func isSkipByte(b byte) bool {
	return b == ' ' || b == '\t' || b == '\r' || b == '\n'
}

func tokenEnd(src []byte, start int) int {
	end := start
	for end < len(src) && isHeaderByte(src[end]) {
		end++
	}
	return end
}

func isHeaderByte(b byte) bool {
	return b == '-' || isNameByte(b)
}

func matchKind(token string) (string, bool) {
	if token == "" {
		return "", false
	}
	for i := range gen.Kinds {
		for j := range gen.Kinds[i].Headers {
			if headerMatches(token, &gen.Kinds[i].Headers[j]) {
				return gen.Kinds[i].ID, true
			}
		}
	}
	return "", false
}

func headerMatches(token string, header *gen.KindHeader) bool {
	if header.Insensitive {
		return equalFoldASCII(token, header.Text)
	}
	return token == header.Text
}

func equalFoldASCII(a, b string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range len(a) {
		if foldASCII(a[i]) != foldASCII(b[i]) {
			return false
		}
	}
	return true
}

func foldASCII(b byte) byte {
	if b >= 'A' && b <= 'Z' {
		return b + ('a' - 'A')
	}
	return b
}

func unknownKindDiagnostic(span source.Span, token string) diag.Diagnostic {
	row := diagnosticRow(codeUnknownKind)
	return diag.Diagnostic{
		Code:     codeUnknownKind,
		Severity: registrySeverity(row.Severity),
		Message:  strings.ReplaceAll(row.Summary, headerTokenPlaceholder, token),
		Span:     span,
		Help:     row.Help,
	}
}

func emptySourceDiagnostic() diag.Diagnostic {
	row := diagnosticRow(codeEmptySource)
	return diag.Diagnostic{
		Code:     codeEmptySource,
		Severity: registrySeverity(row.Severity),
		Message:  row.Summary,
		Span:     source.Span{},
		Help:     row.Help,
	}
}

func diagnosticRow(code string) gen.Diagnostic {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i]
		}
	}
	return gen.Diagnostic{Code: code, Severity: "error"}
}

func registrySeverity(name string) diag.Severity {
	switch name {
	case "error":
		return diag.SeverityError
	case "warning":
		return diag.SeverityWarning
	case "info":
		return diag.SeverityInfo
	}
	return diag.SeverityError
}
