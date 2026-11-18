package pie

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "pie/unexpected-token"
	codeUnknown      = "pie/unknown-statement"
	codeUnterminated = "pie/unterminated"
)

var metadataFields = map[string]string{"ACC_DESCR": "accDescr", "ACC_TITLE": "accTitle", "TITLE": "title"}

func Parse(src []byte, removed []source.Span) (*Pie, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	p.skipNewlines()
	pie := &Pie{}
	pie.Header = p.header()
	if p.kind() == "showData" {
		p.take()
		pie.ShowData = true
	}
	p.statements(pie)
	pie.Span = source.Span{Start: pie.Header.Span.Start, End: p.contentEnd()}
	return pie, mergeSliceDiagnostics(text, p.diags, sliceDiagnostics(src, removed, pie))
}

type parser struct {
	src    string
	tokens []Token
	at     int
	diags  []diag.Diagnostic
}

func (p *parser) token() Token {
	if p.at < len(p.tokens) {
		return p.tokens[p.at]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) kind() string { return p.token().Kind }

func (p *parser) take() Token {
	t := p.token()
	if p.at < len(p.tokens) {
		p.at++
	}
	return t
}

func (p *parser) skipNewlines() {
	for p.kind() == "NEWLINE" {
		p.at++
	}
}

func (p *parser) contentEnd() int {
	for i := min(p.at, len(p.tokens)) - 1; i >= 0; i-- {
		if p.tokens[i].Kind != "NEWLINE" {
			return p.tokens[i].Span.End
		}
	}
	return 0
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: diagnosticHelp(code)}
}

func diagnosticHelp(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, Diagnostic(code, message, span))
}

func (p *parser) unexpected(expected ...string) {
	token := p.token()
	if token.Kind == "UNTERMINATED" {
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	p.issue(codeUnexpected, "unexpected "+p.src[token.Span.Start:token.Span.End]+", expected one of: "+strings.Join(names, ", "), token.Span)
}

func (p *parser) lineEnd() int {
	for i := p.at; i < len(p.tokens); i++ {
		switch p.tokens[i].Kind {
		case "NEWLINE", "EOF", "UNTERMINATED":
			return p.tokens[i].Span.Start
		}
	}
	return len(p.src)
}

func (p *parser) skipLine() {
	for {
		switch p.kind() {
		case "EOF", "UNTERMINATED":
			return
		case "NEWLINE":
			p.take()
			return
		}
		p.take()
	}
}

func (p *parser) header() Token {
	if p.kind() == "pie" {
		return p.take()
	}
	p.unexpected("pie")
	return Token{}
}

func (p *parser) statements(pie *Pie) {
	for {
		switch p.kind() {
		case "EOF":
			return
		case "UNTERMINATED":
			token := p.token()
			p.issue(codeUnterminated, "unterminated "+token.Text, token.Span)
			return
		case "NEWLINE":
			p.take()
		default:
			p.statementOrUnknown(pie)
		}
	}
}

func (p *parser) statementOrUnknown(pie *Pie) {
	first := p.token()
	var statement *Statement
	switch first.Kind {
	case "ACC_DESCR", "ACC_TITLE", "TITLE":
		statement = p.metadata()
	case "STRING":
		statement = p.section()
	default:
		p.issue(codeUnknown, "unknown statement "+p.src[first.Span.Start:first.Span.End], source.Span{Start: first.Span.Start, End: max(p.lineEnd(), first.Span.End)})
		p.skipLine()
		return
	}
	if statement != nil {
		pie.Body = append(pie.Body, *statement)
	}
}

func (p *parser) reject() *Statement {
	p.skipLine()
	return nil
}

func (p *parser) eol() (EOL, bool) {
	start := p.token().Span.Start
	switch p.kind() {
	case "NEWLINE":
		end := start
		for p.kind() == "NEWLINE" {
			end = p.take().Span.End
		}
		return EOL{Span: source.Span{Start: start, End: end}}, true
	case "EOF":
		return EOL{Span: source.Span{Start: start, End: start}}, true
	}
	return EOL{}, false
}

func (p *parser) section() *Statement {
	label := p.take()
	if p.kind() != ":" {
		p.unexpected(":")
		return p.reject()
	}
	p.take()
	if p.kind() != "NUMBER_PIE" {
		p.unexpected("NUMBER_PIE")
		return p.reject()
	}
	number := p.take()
	end := number.Span.End
	eol, ok := p.eol()
	if !ok {
		p.unexpected("EOF", "NEWLINE")
		return p.reject()
	}
	return &Statement{Span: source.Span{Start: label.Span.Start, End: end}, Kind: &PieSection{Label: label, Number: number, EOL: eol}}
}

func (p *parser) metadata() *Statement {
	group := &TitleAndAccessibilities{}
	var start, end int
	for {
		field, ok := metadataFields[p.kind()]
		if !ok {
			break
		}
		token := p.take()
		eol, ok := p.eol()
		if !ok {
			p.unexpected("EOF", "NEWLINE")
			p.skipLine()
			break
		}
		if len(group.Items) == 0 {
			start = token.Span.Start
		}
		end = token.Span.End
		group.Items = append(group.Items, Metadata{Field: field, Value: token.Text, Span: token.Span, EOL: eol})
	}
	if len(group.Items) == 0 {
		return nil
	}
	return &Statement{Span: source.Span{Start: start, End: end}, Kind: group}
}
