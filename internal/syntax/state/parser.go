package state

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	kindEOF        = "EOF"
	kindNL         = "NL"
	kindStructOpen = "STRUCT_START"
	kindStructStop = "STRUCT_STOP"

	codeUnexpected   = "state/unexpected-token"
	codeUnterminated = "state/unterminated"
	codeMultiword    = "state/multiword-state-name"
	codeNestingDepth = "limit/nesting-depth"

	maxDepth = 64
)

type parser struct {
	src     string
	cleaned *source.Cleaned
	tokens  []Token
	at      int
	diags   []diag.Diagnostic
}

type body struct {
	document   Document
	delimiters Delimiters
}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	cleaned := source.Clean(src, removed)
	p := &parser{src: text, cleaned: cleaned, tokens: lexCleaned(cleaned)}
	for p.kind() == kindNL {
		p.at++
	}
	header, ok := p.expect("SD")
	if !ok {
		header = Token{Kind: "SD"}
	}
	document := p.document(0, header.Span.End)
	if p.kind() == kindStructStop {
		p.unexpected(kindEOF)
	}
	return &Start{Span: source.Span{Start: header.Span.Start, End: len(text)}, Header: header, Document: document}, p.diags
}

func (p *parser) kind() string {
	if p.at < len(p.tokens) {
		return p.tokens[p.at].Kind
	}
	return kindEOF
}

func (p *parser) take() (Token, bool) {
	if p.at >= len(p.tokens) {
		return Token{}, false
	}
	t := p.tokens[p.at]
	p.at++
	return t, true
}

func (p *parser) end() int {
	i := max(p.at-1, 0)
	if i < len(p.tokens) {
		return p.tokens[i].Span.End
	}
	return 0
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: diagnosticHelp(code)})
}

func diagnosticHelp(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}

func (p *parser) lastCode(code string) bool {
	return len(p.diags) > 0 && p.diags[len(p.diags)-1].Code == code
}

func (p *parser) unexpected(expected string) {
	span := source.Span{Start: len(p.src), End: len(p.src)}
	if p.at < len(p.tokens) {
		span = p.tokens[p.at].Span
	}
	p.issue(codeUnexpected, "unexpected "+p.raw(span)+", expected one of: "+expected, span)
}

func (p *parser) raw(span source.Span) string {
	return string(p.cleaned.Slice(span))
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take()
	}
	if p.kind() == kindUnterminated {
		p.unterminated()
	} else {
		p.unexpected(kind)
	}
	return Token{}, false
}

func (p *parser) unterminated() {
	t, ok := p.take()
	if !ok {
		return
	}
	p.issue(codeUnterminated, "unterminated "+t.Text, source.Span{Start: t.Span.Start, End: len(p.src)})
}

func (p *parser) recover() {
	for k := p.kind(); k != kindEOF && k != kindNL && k != kindStructStop; k = p.kind() {
		if k == kindUnterminated && !p.lastCode(codeMultiword) {
			p.unterminated()
		} else {
			p.at++
		}
	}
}

func isInvalidTail(kind string) bool {
	switch kind {
	case "-->", "INVALID", "STYLE_SEPARATOR", "DESCR", "STRING", "AS", kindStructOpen:
		return true
	}
	return false
}

func (p *parser) document(depth, start int) Document {
	var lines []Line
	for k := p.kind(); k != kindEOF && k != kindStructStop; k = p.kind() {
		if k == kindNL {
			lines = append(lines, Line{Span: p.tokens[p.at].Span})
			p.at++
			continue
		}
		before := p.at
		if statement := p.lineStatement(depth); statement != nil {
			lines = append(lines, Line{Span: statement.Span, Statement: statement})
		}
		if p.at == before {
			p.at++
		}
	}
	span := source.Span{Start: start, End: start}
	if len(lines) > 0 {
		span = source.Span{Start: lines[0].Span.Start, End: lines[len(lines)-1].Span.End}
	}
	return Document{Span: span, Lines: lines}
}

func (p *parser) lineStatement(depth int) *Statement {
	errors := len(p.diags)
	statement := p.statement(depth)
	invalidTail := isInvalidTail(p.kind())
	if invalidTail && len(p.diags) == errors {
		p.unexpected("NL, STRUCT_STOP")
	}
	if invalidTail || statement == nil {
		p.recover()
		return nil
	}
	return statement
}

func (p *parser) body(depth int) *body {
	open, ok := p.expect(kindStructOpen)
	if !ok {
		return nil
	}
	if depth >= maxDepth {
		p.issue(codeNestingDepth, "nesting depth exceeds 64", open.Span)
		p.at = len(p.tokens)
		return nil
	}
	document := p.document(depth+1, open.Span.End)
	if p.kind() == kindEOF {
		if !p.lastCode(codeNestingDepth) {
			p.issue(codeUnterminated, "unterminated {", source.Span{Start: open.Span.Start, End: len(p.src)})
		}
		return nil
	}
	closer, ok := p.expect(kindStructStop)
	if !ok {
		return nil
	}
	return &body{document: document, delimiters: Delimiters{Open: open.Span, Close: closer.Span}}
}
