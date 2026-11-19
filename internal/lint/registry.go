package lint

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Row = gen.LintRule

const (
	severityOff   = "off"
	sourceMaid    = "maid:"
	prefixMeta    = "meta/"
	codeUnknown   = "meta/unknown-rule"
	codeUnused    = "meta/unused-suppression"
	codeMalformed = "meta/malformed-suppression"
	placeholder   = "CODE"
)

type codeEntry struct {
	canonical string
	lint      *gen.LintRule
	syntax    *gen.Diagnostic
}

type codeTable struct {
	entries map[string]*codeEntry
	alias   map[string]string
}

var codes = newCodeTable()

func newCodeTable() *codeTable {
	t := &codeTable{
		entries: make(map[string]*codeEntry, len(gen.LintRules)+len(gen.Diagnostics)),
		alias:   make(map[string]string, len(gen.LintRules)+len(gen.Diagnostics)),
	}
	for i := range gen.LintRules {
		row := &gen.LintRules[i]
		t.entry(row.Code).lint = row
		t.link(row.Code, row.Aliases)
	}
	for i := range gen.Diagnostics {
		row := &gen.Diagnostics[i]
		t.entry(row.Code).syntax = row
		t.link(row.Code, row.Aliases)
	}
	return t
}

func (t *codeTable) entry(code string) *codeEntry {
	e, ok := t.entries[code]
	if !ok {
		e = &codeEntry{canonical: code}
		t.entries[code] = e
	}
	return e
}

func (t *codeTable) link(code string, aliases []string) {
	t.alias[code] = code
	for _, a := range aliases {
		if _, taken := t.alias[a]; !taken {
			t.alias[a] = code
		}
	}
}

func lookup(code string) (*codeEntry, bool) {
	canonical, ok := codes.alias[code]
	if !ok {
		return nil, false
	}
	return codes.entries[canonical], true
}

func canonical(code string) string {
	if c, ok := codes.alias[code]; ok {
		return c
	}
	return code
}

func (e *codeEntry) suppressible() bool {
	if strings.HasPrefix(e.canonical, prefixMeta) {
		return false
	}
	if e.syntax != nil && e.syntax.Severity == "error" {
		return false
	}
	return e.lint == nil || e.lint.Severity != "error" || !strings.HasPrefix(e.lint.Source, sourceMaid)
}

func suppressibleCode(code string) bool {
	e, ok := lookup(code)
	return ok && e.suppressible()
}

func syntaxRow(row Row) bool {
	return strings.HasPrefix(row.Source, sourceMaid)
}

func metaRow(row Row) bool {
	return strings.HasPrefix(row.Code, prefixMeta)
}

func severityOf(name string) diag.Severity {
	switch name {
	case "error":
		return diag.SeverityError
	case "info":
		return diag.SeverityInfo
	}
	return diag.SeverityWarning
}

func fill(row Row, value string) string {
	return strings.Replace(row.Summary, placeholder, value, 1)
}

func diagnostic(row Row, message string, span source.Span) diag.Diagnostic {
	return diag.Diagnostic{Code: row.Code, Message: message, Span: span, Help: row.Help}
}
