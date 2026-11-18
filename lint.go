package mermaid

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/lint"
)

func Lint(d *Document, cfg LintConfig) []Diagnostic {
	return publicDiagnostics(lint.Run(lint.AnalyzeDiagram(d.diagram), cfg.internal()).Lint)
}

func ApplyFixes(src []byte, cfg LintConfig, limit FixSafety) ([]byte, int) {
	return lint.ApplyFixes(src, cfg.internal(), diag.FixSafety(limit))
}

func (c LintConfig) internal() lint.Config {
	severity := make(map[string]diag.Severity, len(c.Severity))
	for code, s := range c.Severity {
		severity[code] = diag.Severity(s)
	}
	return lint.Config{Select: c.Select, Ignore: c.Ignore, Severity: severity, Off: c.Off}
}
