package timeline

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "timeline/unexpected-token"
	codeUnknown      = "timeline/unknown-statement"
	codeUnterminated = "timeline/unterminated"
)

var headerTokens = []string{kindTimeline, kindTimelineLR, kindTimelineTD}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, scan: newScanner(text, removed)}
	p.advance()
	return p.start(), p.diags
}

type parser struct {
	src   string
	scan  *scanner
	tok   Token
	diags []diag.Diagnostic
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

func (p *parser) advance() { p.tok = p.scan.next() }

func (p *parser) take() Token {
	t := p.tok
	p.advance()
	return t
}

func (p *parser) describe(t Token) string {
	if t.Span.Start == t.Span.End {
		return "end of input"
	}
	return p.src[t.Span.Start:t.Span.End]
}

func (p *parser) unexpected(expected []string) {
	names := slices.Clone(expected)
	slices.Sort(names)
	message := "unexpected " + p.describe(p.tok) + ", expected one of: " + strings.Join(names, ", ")
	p.diags = append(p.diags, Diagnostic(codeUnexpected, message, p.tok.Span))
}

func (p *parser) start() *Start {
	for p.tok.Kind == kindNewline {
		p.advance()
	}
	if !slices.Contains(headerTokens, p.tok.Kind) {
		p.unexpected(headerTokens)
		return &Start{Span: source.Span{Start: p.tok.Span.Start, End: len(p.src)}}
	}
	token := p.take()
	document := p.document()
	return &Start{
		Span:     source.Span{Start: token.Span.Start, End: max(document.Span.End, token.Span.End)},
		Header:   TimelineHeader{Token: token, Direction: direction(token.Kind)},
		Document: document,
	}
}

func direction(kind string) string {
	switch kind {
	case kindTimelineLR:
		return "LR"
	case kindTimelineTD:
		return "TD"
	}
	return ""
}

func (p *parser) document() Document {
	doc := Document{Span: source.Span{Start: p.tok.Span.Start, End: p.tok.Span.Start}}
	for p.tok.Kind != kindEOF {
		if line, ok := p.line(); ok {
			doc.Lines = append(doc.Lines, line)
			doc.Span.End = max(doc.Span.End, line.Span.End)
		}
	}
	return doc
}

func (p *parser) line() (Line, bool) {
	switch p.tok.Kind {
	case kindNewline:
		separator := p.take()
		return Line{Span: separator.Span, Separator: &separator}, true
	case kindOpen:
		t := p.take()
		p.diags = append(p.diags, Diagnostic(codeUnterminated, "unterminated "+t.Text, t.Span))
		return Line{}, false
	}
	statement, ok := p.statement()
	if !ok {
		return Line{}, false
	}
	return Line{Span: statement.Span, Statement: &statement}, true
}

func (p *parser) statement() (Statement, bool) {
	switch p.tok.Kind {
	case kindTitle:
		t := p.take()
		return Statement{Span: t.Span, Kind: &Title{Token: t}}, true
	case kindSection:
		t := p.take()
		return Statement{Span: t.Span, Kind: &Section{Token: t}}, true
	case kindPeriod:
		t := p.take()
		return Statement{Span: t.Span, Kind: &PeriodStatement{Token: t}}, true
	case kindEvent:
		t := p.take()
		return Statement{Span: t.Span, Kind: &EventStatement{Token: t}}, true
	case kindAccBlockV:
		v := p.take()
		return Statement{Span: source.Span{Start: v.Open.Start, End: v.Close.End}, Kind: &AccDescrBlock{Value: v}}, true
	case kindAccTitle:
		return p.accessibility(kindAccTitleV, func(o, v Token) StatementKind { return &AccTitle{Opener: o, Value: v} })
	case kindAccDescr:
		return p.accessibility(kindAccDescrV, func(o, v Token) StatementKind { return &AccDescr{Opener: o, Value: v} })
	}
	p.unknown()
	return Statement{}, false
}

func (p *parser) accessibility(value string, build func(opener, value Token) StatementKind) (Statement, bool) {
	opener := p.take()
	if p.tok.Kind != value {
		p.unexpected([]string{value})
		return Statement{}, false
	}
	v := p.take()
	return Statement{Span: source.Span{Start: opener.Span.Start, End: max(opener.Span.End, v.Span.End)}, Kind: build(opener, v)}, true
}

func (p *parser) unknown() {
	first := p.tok
	end := p.scan.skipLine(first.Span.End)
	p.advance()
	p.diags = append(p.diags, Diagnostic(codeUnknown, "unknown statement "+p.describe(first), source.Span{Start: first.Span.Start, End: end}))
}
