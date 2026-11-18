package sankey

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "sankey/unexpected-token"
	codeUnknown      = "sankey/unknown-statement"
	codeUnterminated = "sankey/unterminated"

	fieldCount = 3
)

var fieldStarts = []string{"DQUOTE", "NON_ESCAPED_TEXT"}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	return p.start(), p.diags
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

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	help := ""
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			help = gen.Diagnostics[i].Help
		}
	}
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: help}
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, Diagnostic(code, message, span))
}

func (p *parser) boundary() bool {
	switch p.kind() {
	case "NEWLINE", "EOF", "UNTERMINATED":
		return true
	}
	return false
}

func (p *parser) recover() {
	for !p.boundary() {
		p.take()
	}
}

func (p *parser) unexpected(expected ...string) {
	token := p.token()
	if token.Kind == "UNTERMINATED" {
		p.unterminated()
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	p.issue(codeUnexpected, "unexpected "+p.src[token.Span.Start:token.Span.End]+", expected one of: "+strings.Join(names, ", "), token.Span)
	p.recover()
}

func (p *parser) unterminated() {
	token := p.take()
	p.issue(codeUnterminated, "unterminated "+token.Text, token.Span)
}

func (p *parser) unknownStatement() {
	first := p.take()
	end := first.Span.End
	for !p.boundary() {
		end = p.take().Span.End
	}
	p.issue(codeUnknown, "unknown statement "+first.Text, source.Span{Start: first.Span.Start, End: end})
}

func (p *parser) start() *Start {
	first := p.token().Span.Start
	header, ok := p.header()
	var csv Csv
	if ok || p.kind() != "EOF" {
		csv = p.csv()
	}
	for p.kind() == "UNTERMINATED" {
		p.unterminated()
	}
	eof := p.token()
	return &Start{
		Span:   source.Span{Start: first, End: len(p.src)},
		Header: header,
		Csv:    csv,
		OptEof: OptEof{Span: source.Span{Start: eof.Span.Start, End: eof.Span.End}, Present: eof.Kind == "EOF"},
	}
}

func (p *parser) header() (Token, bool) {
	if p.kind() != "SANKEY" {
		p.unexpected("SANKEY")
		return Token{}, false
	}
	header := p.take()
	if p.kind() == "NEWLINE" {
		p.take()
		return header, true
	}
	p.unexpected("NEWLINE")
	if p.kind() == "NEWLINE" {
		p.take()
	}
	return header, false
}

func (p *parser) csv() Csv {
	start := p.token().Span.Start
	var records []Record
	for {
		if rec, ok := p.record(len(records)); ok {
			records = append(records, rec)
		}
		if p.kind() != "NEWLINE" {
			break
		}
		p.take()
	}
	end := start
	if n := len(records); n > 0 {
		end = records[n-1].Span.End
	}
	return Csv{Span: source.Span{Start: start, End: end}, Records: records}
}

func (p *parser) record(index int) (Record, bool) {
	if p.kind() == "INVALID" {
		p.unknownStatement()
		return Record{}, false
	}
	var fields [fieldCount]Field
	for i := range fields {
		if i > 0 && !p.comma() {
			return Record{}, false
		}
		field, ok := p.field()
		if !ok {
			return Record{}, false
		}
		fields[i] = field
	}
	if k := p.kind(); k != "NEWLINE" && k != "EOF" {
		p.unexpected("EOF", "NEWLINE")
		return Record{}, false
	}
	span := source.Span{Start: fields[0].Span.Start, End: fields[fieldCount-1].Span.End}
	return Record{Span: span, Source: fields[0], Target: fields[1], Value: fields[2], Index: index}, true
}

func (p *parser) comma() bool {
	if p.kind() == "COMMA" {
		p.take()
		return true
	}
	p.unexpected("COMMA")
	return false
}

func (p *parser) field() (Field, bool) {
	switch p.kind() {
	case "COMMA", "NEWLINE", "EOF":
		at := p.token().Span.Start
		span := source.Span{Start: at, End: at}
		return Field{Span: span, NonEscaped: &NonEscaped{Span: span}}, true
	case "NON_ESCAPED_TEXT":
		t := p.take()
		return Field{Span: t.Span, NonEscaped: &NonEscaped{Span: t.Span, Text: t.Text}}, true
	case "DQUOTE":
		return p.escaped()
	}
	p.unexpected(fieldStarts...)
	return Field{}, false
}

func (p *parser) escaped() (Field, bool) {
	open := p.take()
	content := Token{}
	if p.kind() == "ESCAPED_TEXT" {
		content = p.take()
	}
	if p.kind() != "DQUOTE" {
		p.unexpected("DQUOTE")
		return Field{}, false
	}
	closing := p.take()
	span := source.Span{Start: open.Span.Start, End: closing.Span.End}
	return Field{Span: span, Escaped: &Escaped{Span: span, Text: content.Text}}, true
}
