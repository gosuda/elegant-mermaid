package sequence

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeQuoteUnclosed = "sequence/quote-unclosed"
	closeQuoteTitle   = "Insert the closing quote"
	doubleQuote       = `"`
	blanks            = " \t"
)

func (p *parser) checkQuotes(actor Actor, alias *Alias) {
	p.unclosedQuote(actor.Span)
	if alias != nil {
		p.unclosedQuote(alias.Text.Span)
	}
}

func (p *parser) unclosedQuote(token source.Span) {
	span := p.trimmed(token)
	text := p.src[span.Start:span.End]
	if !strings.HasPrefix(text, doubleQuote) || strings.Count(text, doubleQuote)%2 == 0 {
		return
	}
	row := lintRow(codeQuoteUnclosed)
	p.diags = append(p.diags, diag.Diagnostic{
		Code:     codeQuoteUnclosed,
		Severity: diag.SeverityWarning,
		Message:  row.Summary,
		Span:     span,
		Help:     row.Help,
		Fixes: []diag.Fix{{
			Title:  closeQuoteTitle,
			Safety: diag.FixUnsafe,
			Edits:  []diag.Edit{{Span: source.Span{Start: span.End, End: span.End}, NewText: doubleQuote}},
		}},
	})
}

func (p *parser) trimmed(span source.Span) source.Span {
	raw := p.src[span.Start:span.End]
	lead := len(raw) - len(strings.TrimLeft(raw, blanks))
	body := strings.TrimRight(raw[lead:], blanks)
	return source.Span{Start: span.Start + lead, End: span.Start + lead + len(body)}
}

func lintRow(code string) gen.LintRule {
	for i := range gen.LintRules {
		if gen.LintRules[i].Code == code {
			return gen.LintRules[i]
		}
	}
	return gen.LintRule{}
}
