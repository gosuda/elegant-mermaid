package journey

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "journey/unexpected-token"
	codeUnknown      = "journey/unknown-statement"
	codeUnterminated = "journey/unterminated"
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(newView(text, removed))}
	p.skipNewlines()
	start := &Start{Header: p.header()}
	end := start.Header.Span.End
	start.Document.Span = source.Span{Start: end, End: end}
	p.document(&start.Document)
	start.Span = source.Span{Start: start.Header.Span.Start, End: max(end, start.Document.Span.End)}
	return start, p.diags
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
	return Token{Kind: kindEOF, Span: source.Span{Start: len(p.src), End: len(p.src)}, end: len(p.src)}
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
	for p.kind() == kindNewline {
		p.at++
	}
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

func describe(t Token) string {
	switch t.Kind {
	case kindEOF:
		return "end of input"
	case kindNewline:
		return "end of line"
	}
	return t.Text
}

func (p *parser) unexpected(expected string) {
	t := p.token()
	p.issue(codeUnexpected, "unexpected "+describe(t)+", expected one of: "+expected, t.Span)
	p.recover(t)
}

func (p *parser) recover(from Token) {
	for p.kind() != kindEOF && p.kind() != kindNewline && p.token().Span.Start < from.end {
		p.take()
	}
}

func (p *parser) header() Token {
	if p.kind() != kindJourney {
		p.unexpected(kindJourney)
		return Token{Span: source.Span{Start: p.token().Span.Start, End: p.token().Span.Start}}
	}
	return p.take()
}

func (p *parser) document(doc *Document) {
	for p.kind() != kindEOF {
		if line, ok := p.line(); ok {
			doc.Lines = append(doc.Lines, line)
		}
	}
	if n := len(doc.Lines); n > 0 {
		doc.Span = source.Span{Start: doc.Lines[0].Span.Start, End: doc.Lines[n-1].Span.End}
	}
}

func (p *parser) line() (Line, bool) {
	first := p.token()
	if first.Kind == kindNewline {
		p.take()
		return Line{Span: first.Span}, true
	}
	kind, last, known := p.statement(first)
	if !known {
		p.issue(codeUnknown, "unknown statement "+first.Text, source.Span{Start: first.Span.Start, End: max(first.end, first.Span.End)})
		p.take()
		p.recover(first)
		return Line{}, false
	}
	if kind == nil {
		return Line{}, false
	}
	span := source.Span{Start: first.Span.Start, End: last}
	return Line{Span: span, Statement: &Statement{Span: span, Kind: kind}}, true
}

func (p *parser) statement(first Token) (StatementKind, int, bool) {
	switch first.Kind {
	case kindTitle:
		p.take()
		return &Title{Text: first.Value}, first.Span.End, true
	case kindSection:
		p.take()
		return &Section{Text: first.Value}, first.Span.End, true
	case kindAccTitle:
		p.take()
		value := p.take()
		return &AccTitle{Keyword: first.Span, Value: value.Value}, value.Span.End, true
	case kindAccDescr:
		p.take()
		value := p.take()
		return &AccDescr{Keyword: first.Span, Value: value.Value}, value.Span.End, true
	case kindOpen:
		return p.multiline()
	case kindTaskName:
		return p.task()
	}
	return nil, 0, false
}

func (p *parser) multiline() (StatementKind, int, bool) {
	open := p.take()
	node := &AccDescrMultiline{Open: open.Span}
	end := open.Span.End
	hasValue := p.kind() == kindMultiline
	if hasValue {
		value := p.take()
		node.Value, end = value.Value, value.Span.End
	}
	switch p.kind() {
	case kindClose:
		closing := p.take().Span
		node.Close, end = &closing, closing.End
	case kindUnclosed:
		t := p.take()
		p.issue(codeUnterminated, "unterminated "+t.Text, t.Span)
		end = t.Span.End
	}
	if !hasValue {
		return nil, 0, true
	}
	return node, end, true
}

func (p *parser) task() (StatementKind, int, bool) {
	name := p.take()
	if p.kind() != kindTaskData {
		p.unexpected(kindTaskData)
		return nil, 0, true
	}
	data := p.take()
	return &Task{Name: name.Value, Data: data.Value, Fields: data.Fields}, data.Span.End, true
}
