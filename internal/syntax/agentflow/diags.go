package agentflow

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func diagnostic(code, message string, span source.Span) diag.Diagnostic {
	return Diagnostic(code, message, span)
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	help := ""
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			help = gen.Diagnostics[i].Help
			break
		}
	}
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: help}
}
