package flowchart

import (
	evdiag "github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/interaction"
)

const (
	codeUnsafeURL       = "interaction/unsafe-url"
	codeCallbackIgnored = "interaction/callback-ignored"
)

func interactionDiagnostics(c Click) []evdiag.Diagnostic {
	switch {
	case c.Kind == ClickCallback && c.Callback != "":
		return []evdiag.Diagnostic{interactionDiagnostic(codeCallbackIgnored, evdiag.SeverityInfo, "callback "+c.Callback+" is ignored", c)}
	case c.Kind == ClickLink && c.ActionSpan.End > c.ActionSpan.Start:
		if _, ok := interaction.SafeURL(c.URL); !ok {
			return []evdiag.Diagnostic{interactionDiagnostic(codeUnsafeURL, evdiag.SeverityWarning, "link URL is not allowed", c)}
		}
	}
	return nil
}

func interactionDiagnostic(code string, severity evdiag.Severity, message string, c Click) evdiag.Diagnostic {
	return evdiag.Diagnostic{Code: code, Severity: severity, Message: message, Span: c.ActionSpan, Help: registryHelp(code)}
}

func registryHelp(code string) string {
	for _, row := range gen.Diagnostics {
		if row.Code == code {
			return row.Help
		}
	}
	return ""
}
