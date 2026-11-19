package swimlane

import "github.com/gosuda/elegant-mermaid/internal/diag"

func diagnosticOf(code string) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Help: "help"}
}
