package lint

import "github.com/gosuda/elegant-mermaid/internal/diag"

func ApplyHostFixes(host []byte, cfg Config, limit diag.FixSafety) ([]byte, int) {
	return applyFixes(host, cfg, limit, analyzeHost)
}

func analyzeHost(host []byte, cfg Config) ([]byte, []diag.Diagnostic) {
	report := LintHost(host, cfg)
	return report.Source, report.Diagnostics
}
