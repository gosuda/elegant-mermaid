package c4

import (
	"fmt"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type parser struct {
	src     []byte
	cleaned *source.Cleaned
	tokens  []Token
	at      int
	diags   []diag.Diagnostic
}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	cleaned := source.Clean(src, removed)
	p := parser{src: src, cleaned: cleaned, tokens: lex(cleaned)}
	p.newlines()
	var start *Start
	if strings.HasPrefix(p.kind(), "direction_") {
		start = p.direction()
	} else {
		start = p.mermaidDoc()
	}
	diag.Sort(p.diags)
	return start, p.diags
}

func (p *parser) kind() string {
	if p.at >= len(p.tokens) {
		return "EOF"
	}
	return p.tokens[p.at].Kind
}

func (p *parser) take() Token {
	if p.at >= len(p.tokens) {
		end := len(p.src)
		return Token{Kind: "EOF", Span: source.Span{Start: end, End: end}}
	}
	t := p.tokens[p.at]
	p.at++
	return t
}

func (p *parser) end() int {
	if p.at == 0 || p.at > len(p.tokens) {
		return 0
	}
	return p.tokens[p.at-1].Span.End
}

func (p *parser) span() source.Span {
	if p.at >= len(p.tokens) {
		end := len(p.src)
		return source.Span{Start: end, End: end}
	}
	return p.tokens[p.at].Span
}

func (p *parser) text(span source.Span) string {
	if span.Start < 0 || span.End < span.Start || span.End > len(p.src) {
		return ""
	}
	return string(p.cleaned.Slice(span))
}

func (p *parser) newlines() {
	for p.kind() == "NEWLINE" {
		p.at++
	}
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span})
}

func (p *parser) unexpected(expected string) {
	if p.enclosingUnterminated() {
		return
	}
	span := p.span()
	p.issue("c4/unexpected-token", fmt.Sprintf("unexpected %s, expected one of: %s", p.text(span), expected), span)
}

func (p *parser) enclosingUnterminated() bool {
	span := p.span()
	for i := p.at; i < len(p.tokens); i++ {
		t := p.tokens[i]
		if t.Kind == "UNTERMINATED" && t.Span.Start <= span.Start && span.End <= t.Span.End {
			p.at = i
			p.unterminated()
			return true
		}
	}
	return false
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take(), true
	}
	p.unexpected(kind)
	return Token{}, false
}

func (p *parser) unterminated() {
	if p.at >= len(p.tokens) {
		return
	}
	t := p.take()
	p.issue("c4/unterminated", "unterminated "+string(t.Raw), t.Span)
}

func (p *parser) recover() {
	for {
		switch p.kind() {
		case "NEWLINE", "RBRACE", "EOF":
			return
		case "UNTERMINATED":
			p.unterminated()
		default:
			p.at++
		}
	}
}

func (p *parser) direction() *Start {
	t := p.take()
	span := t.Span
	p.newlines()
	if p.kind() != "EOF" {
		p.unexpected("EOF")
	}
	return &Start{Span: span, Direction: &Direction{Span: span, Direction: t}}
}

func (p *parser) mermaidDoc() *Start {
	header := p.header()
	p.expect("NEWLINE")
	statements := p.statements(0)
	span := source.Span{Start: header.Span.Start, End: max(statements.Span.End, header.Span.End)}
	graph := GraphConfig{Span: span, Header: header, Statements: statements}
	return &Start{Span: span, MermaidDoc: &MermaidDoc{Span: span, GraphConfig: graph}}
}

func (p *parser) header() Token {
	switch p.kind() {
	case "C4_CONTEXT", "C4_CONTAINER", "C4_COMPONENT", "C4_DYNAMIC", "C4_DEPLOYMENT":
		return p.take()
	}
	p.unexpected("C4_COMPONENT, C4_CONTAINER, C4_CONTEXT, C4_DEPLOYMENT, C4_DYNAMIC")
	return Token{Kind: "C4_CONTEXT", Span: p.span()}
}

func (p *parser) statements(depth int) Statements {
	start := p.span().Start
	var items []Statement
	p.newlines()
	for p.kind() != "EOF" {
		if p.closingBoundary(depth) {
			break
		}
		before := p.at
		if s, ok := p.statementLine(depth); ok {
			items = append(items, s)
		}
		if p.at == before {
			p.at++
		}
		p.newlines()
	}
	if depth == 0 && len(items) == 0 && len(p.diags) == 0 {
		p.unexpected("diagramStatement, otherStatement")
	}
	span := source.Span{Start: start, End: start}
	if len(items) > 0 {
		span.Start, span.End = items[0].Span.Start, items[len(items)-1].Span.End
	}
	return Statements{Span: span, Items: items}
}

func (p *parser) statementLine(depth int) (Statement, bool) {
	s, ok := p.statement(depth)
	switch p.kind() {
	case "NEWLINE", "RBRACE", "EOF":
		if !ok {
			p.recover()
		}
		return s, ok
	}
	if ok {
		p.unexpected("EOF, NEWLINE, RBRACE")
	}
	p.recover()
	return Statement{}, false
}

func (p *parser) closingBoundary(depth int) bool {
	if p.kind() != "RBRACE" {
		return false
	}
	if depth > 0 {
		return true
	}
	p.unexpected("EOF")
	p.at++
	p.newlines()
	return p.kind() == "EOF"
}

func (p *parser) statement(depth int) (Statement, bool) {
	if p.kind() == "UNTERMINATED" {
		p.unterminated()
		return Statement{}, false
	}
	if isOther(p.kind()) {
		if other := p.other(); other != nil {
			return Statement{Span: other.Span, Other: other}, true
		}
		return Statement{}, false
	}
	if isMacroKind(p.kind()) {
		if diagram := p.diagram(depth); diagram != nil {
			return Statement{Span: diagram.Span, Diagram: diagram}, true
		}
		return Statement{}, false
	}
	token := p.take()
	p.recover()
	end := max(p.end(), token.Span.End)
	p.issue("c4/unknown-statement", "unknown statement "+string(token.Raw), source.Span{Start: token.Span.Start, End: end})
	return Statement{}, false
}

func isOther(kind string) bool {
	switch kind {
	case "title", "accDescription", "acc_title", "acc_descr", "acc_descr_multiline_value":
		return true
	}
	return false
}

func (p *parser) other() *OtherStatement {
	token := p.take()
	value := Token{}
	ok := true
	switch token.Kind {
	case "acc_title":
		value, ok = p.expect("acc_title_value")
	case "acc_descr":
		value, ok = p.expect("acc_descr_value")
	case "title":
		value = p.textValue(token, len("title"))
	case "accDescription":
		value = p.textValue(token, len("accDescription"))
	default:
		value = token
	}
	if !ok {
		return nil
	}
	return &OtherStatement{Span: source.Span{Start: token.Span.Start, End: value.Span.End}, Form: token.Kind, Value: value}
}

func (p *parser) textValue(token Token, keyword int) Token {
	size := keyword
	if width := separatorWidth(token.Raw[keyword:]); width > 0 {
		size += width
	}
	begin := p.cleaned.Index(token.Span.Start) + size
	return Token{Kind: token.Kind, Span: source.Span{Start: p.cleaned.Offset(begin), End: token.Span.End}, Raw: token.Raw[size:]}
}

func separatorWidth(b []byte) int {
	r, size := utf8.DecodeRune(b)
	if size > 0 && unicode.IsSpace(r) {
		return size
	}
	return 0
}

func (p *parser) diagram(depth int) *DiagramStatement {
	macro := p.take()
	attributes, ok := p.attributes()
	if !ok {
		return nil
	}
	span := source.Span{Start: macro.Span.Start, End: attributes.Span.End}
	if !isBoundaryKind(macro.Kind) {
		return &DiagramStatement{Span: span, Call: &CallStatement{Span: span, Macro: macro, Attributes: attributes}}
	}
	start := BoundaryStart{Span: span, Macro: macro, Attributes: attributes}
	boundary := p.boundary(start, depth)
	if boundary == nil {
		return nil
	}
	return &DiagramStatement{Span: boundary.Span, Boundary: boundary}
}

func (p *parser) attributes() (Attributes, bool) {
	open, ok := p.expect("LPAREN")
	if !ok {
		return Attributes{}, false
	}
	var items []Attribute
	for isAttributeStart(p.kind()) {
		attribute, ok := p.attribute()
		if !ok {
			return Attributes{}, false
		}
		items = append(items, attribute)
	}
	if p.kind() == "UNTERMINATED" {
		p.unterminated()
		return Attributes{}, false
	}
	if len(items) == 0 {
		p.unexpected("ATTRIBUTE_EMPTY, STR, STR_KEY")
		return Attributes{}, false
	}
	close, ok := p.expect("RPAREN")
	if !ok {
		return Attributes{}, false
	}
	return Attributes{Span: source.Span{Start: open.Span.Start, End: close.Span.End}, Items: items}, true
}

func isAttributeStart(kind string) bool {
	return kind == "STR" || kind == "STR_KEY" || kind == "ATTRIBUTE_EMPTY"
}

func (p *parser) attribute() (Attribute, bool) {
	token := p.take()
	attribute := Attribute{}
	switch token.Kind {
	case "STR_KEY":
		value, ok := p.expect("STR_VALUE")
		if !ok {
			return Attribute{}, false
		}
		key := token
		attribute.Key, attribute.Value = &key, &value
	case "ATTRIBUTE_EMPTY":
		empty := token
		attribute.Empty = &empty
	default:
		positional := token
		attribute.Positional = &positional
	}
	attribute.Span = source.Span{Start: token.Span.Start, End: p.end()}
	return attribute, true
}

func (p *parser) boundary(start BoundaryStart, depth int) *BoundaryStatement {
	brace, ok := p.boundaryBrace()
	if !ok {
		return nil
	}
	if depth >= 64 {
		p.issue("limit/nesting-depth", "nesting depth exceeds 64", brace.Span)
		p.at = len(p.tokens)
		return nil
	}
	begin := start.Span.Start
	startStatement := BoundaryStartStatement{Span: source.Span{Start: begin, End: brace.Span.End}, Start: start, Brace: brace}
	startsWithDiagram := isMacroKind(p.kind())
	if !startsWithDiagram && p.kind() != "EOF" {
		p.unexpected("diagramStatement")
	}
	statements := p.statements(depth + 1)
	if p.kind() == "EOF" {
		p.openBoundaryError(startStatement.Brace.Span)
		return nil
	}
	close, ok := p.expect("RBRACE")
	if !ok || !startsWithDiagram {
		return nil
	}
	body := DiagramStatements(statements)
	return &BoundaryStatement{
		Span:  source.Span{Start: begin, End: close.Span.End},
		Start: startStatement,
		Body:  body,
		Stop:  BoundaryStopStatement{Span: close.Span, Close: close},
	}
}

func (p *parser) boundaryBrace() (Token, bool) {
	if p.kind() == "NEWLINE" {
		p.at++
		brace, ok := p.expect("LBRACE")
		if !ok {
			return Token{}, false
		}
		if p.kind() == "NEWLINE" {
			p.at++
		}
		return brace, true
	}
	brace, ok := p.expect("LBRACE")
	if !ok {
		return Token{}, false
	}
	if p.kind() == "EOF" {
		p.openBoundaryError(brace.Span)
		return Token{}, false
	}
	if _, ok := p.expect("NEWLINE"); !ok {
		return Token{}, false
	}
	return brace, true
}

func (p *parser) openBoundaryError(open source.Span) {
	for _, d := range p.diags {
		if d.Code == "limit/nesting-depth" {
			return
		}
	}
	p.issue("c4/unterminated", "unterminated {", source.Span{Start: open.Start, End: len(p.src)})
}
