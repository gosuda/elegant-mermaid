package block

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeNesting      = "limit/nesting-depth"
	codeUnexpected   = "block/unexpected-token"
	codeUnknown      = "block/unknown-statement"
	codeUnterminated = "block/unterminated"

	maxDepth = 64
)

var statementStarts = []string{"BLOCK_DIAGRAM_KEY", "COLUMNS", "NODE_ID", "SPACE_BLOCK", "class", "classDef", "id-block", "style"}

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, tokens: lex(text, removed)}
	header, ok := p.expect("BLOCK_DIAGRAM_KEY")
	if !ok {
		header = Token{Kind: "BLOCK_DIAGRAM_KEY"}
	}
	document := p.document()
	return &Start{Span: source.Span{Start: header.Span.Start, End: p.contentEnd(header.Span.End)}, Header: header, Document: document}, p.diags
}

type parser struct {
	src    string
	tokens []Token
	at     int
	depth  int
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

func (p *parser) contentEnd(floor int) int {
	end := floor
	for _, statement := range p.tokens[:min(p.at, len(p.tokens))] {
		if statement.Kind != "EOF" && statement.Kind != "UNTERMINATED" {
			end = max(end, statement.Span.End)
		}
	}
	return end
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	d := diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span}
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			d.Help = gen.Diagnostics[i].Help
			d.Severity = severity(gen.Diagnostics[i].Severity)
		}
	}
	return d
}

func severity(word string) diag.Severity {
	switch word {
	case "warning":
		return diag.SeverityWarning
	case "info":
		return diag.SeverityInfo
	}
	return diag.SeverityError
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, Diagnostic(code, message, span))
}

func (p *parser) raw(span source.Span) string { return p.src[span.Start:span.End] }

func (p *parser) unexpected(expected ...string) {
	token := p.token()
	if token.Kind == "UNTERMINATED" {
		p.unterminated(token)
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	p.issue(codeUnexpected, "unexpected "+p.raw(token.Span)+", expected one of: "+strings.Join(names, ", "), token.Span)
}

func (p *parser) unterminated(opener Token) {
	if slices.ContainsFunc(p.diags, func(d diag.Diagnostic) bool { return d.Code == codeUnterminated || d.Code == codeNesting }) {
		return
	}
	span := opener.Span
	if opener.Kind != "UNTERMINATED" {
		span.End = len(p.src)
	}
	p.issue(codeUnterminated, "unterminated "+opener.Text, span)
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take(), true
	}
	p.unexpected(kind)
	return Token{}, false
}

func (p *parser) lineEnd(from int) int {
	if i := strings.IndexAny(p.src[min(from, len(p.src)):], "\n\r"); i >= 0 {
		return from + i
	}
	return len(p.src)
}

func (p *parser) closesComposite() bool { return p.depth > 0 && p.kind() == "end" }

func (p *parser) atEnd() bool {
	kind := p.kind()
	return kind == "EOF" || kind == "UNTERMINATED"
}

func (p *parser) recover() {
	if p.atEnd() || p.closesComposite() {
		return
	}
	token := p.take()
	limit := p.lineEnd(token.Span.End)
	for !p.atEnd() && !p.closesComposite() && p.token().Span.Start < limit {
		p.take()
	}
}

func (p *parser) unknownStatement() {
	first := p.token()
	if first.Kind == "UNTERMINATED" {
		p.unterminated(first)
		return
	}
	limit := p.lineEnd(first.Span.End)
	p.recover()
	end := max(first.Span.End, min(limit, p.token().Span.Start))
	p.issue(codeUnknown, "unknown statement "+p.raw(first.Span), source.Span{Start: first.Span.Start, End: end})
}

func (p *parser) document() Document {
	start := p.token().Span.Start
	mark := len(p.diags)
	var statements []Statement
	for !p.atEnd() && !p.closesComposite() {
		before := p.at
		if statement := p.statement(); statement != nil {
			statements = append(statements, *statement)
		} else if p.at == before {
			p.unknownStatement()
		}
	}
	if len(statements) == 0 && len(p.diags) == mark {
		p.unexpected(statementStarts...)
	}
	end := start
	if n := len(statements); n > 0 {
		end = statements[n-1].Span.End
	}
	return Document{Span: source.Span{Start: start, End: end}, Statements: statements}
}

func (p *parser) statement() *Statement {
	start := p.token().Span.Start
	kind, known := p.statementKind()
	if !known || kind == nil {
		return nil
	}
	return &Statement{Span: source.Span{Start: start, End: p.contentEnd(start)}, Kind: kind}
}

func (p *parser) statementKind() (StatementKind, bool) {
	switch p.kind() {
	case "NODE_ID":
		return nilUnless(p.nodeStatement()), true
	case "COLUMNS":
		token := p.take()
		return &ColumnsStatement{Span: token.Span, Token: token}, true
	case "SPACE_BLOCK":
		token := p.take()
		return &SpaceStatement{Span: token.Span, Token: token}, true
	case "BLOCK_DIAGRAM_KEY", "id-block":
		return nilUnless(p.blockStatement()), true
	case "classDef":
		return nilUnless(p.classDefStatement()), true
	case "class":
		return nilUnless(p.cssClassStatement()), true
	case "style":
		return nilUnless(p.styleStatement()), true
	}
	return nil, false
}

func nilUnless[T any, P interface {
	*T
	StatementKind
}](statement P) StatementKind {
	if statement == nil {
		return nil
	}
	return statement
}

func (p *parser) fail(expected ...string) {
	p.unexpected(expected...)
	p.recover()
}

func (p *parser) nodeStatement() *NodeStatement {
	first, ok := p.node()
	if !ok {
		return nil
	}
	statement := &NodeStatement{First: first}
	if p.kind() == "SIZE" {
		size := p.take()
		statement.Size = &size
	}
	for p.kind() == "LINK" || p.kind() == "START_LINK" {
		link, ok := p.link()
		if !ok {
			return nil
		}
		target, ok := p.node()
		if !ok {
			return nil
		}
		statement.Links = append(statement.Links, LinkedNode{Link: link, Node: target})
	}
	if p.kind() == "SIZE" {
		p.fail(append([]string{"EOF", "LINK", "START_LINK", "end"}, statementStarts...)...)
		return nil
	}
	statement.Span = source.Span{Start: first.Span.Start, End: p.contentEnd(first.Span.End)}
	return statement
}

func (p *parser) node() (Node, bool) {
	id, ok := p.expectOrFail("NODE_ID")
	if !ok {
		return Node{}, false
	}
	node := Node{Span: id.Span, ID: id}
	switch p.kind() {
	case "NODE_DSTART":
		shape, ok := p.shape()
		if !ok {
			return Node{}, false
		}
		node.Shape = shape
	case "BLOCK_ARROW_START":
		shape, ok := p.arrowShape()
		if !ok {
			return Node{}, false
		}
		node.Shape = shape
	}
	if node.Shape != nil {
		node.Span.End = node.Shape.Span.End
	}
	return node, true
}

func (p *parser) expectOrFail(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take(), true
	}
	p.fail(kind)
	return Token{}, false
}

func (p *parser) shape() (*NodeShapeNLabel, bool) {
	open := p.take()
	label, ok := p.expectOrFail("STR")
	if !ok {
		return nil, false
	}
	closer, ok := p.expectOrFail("NODE_DEND")
	if !ok {
		return nil, false
	}
	return &NodeShapeNLabel{Span: source.Span{Start: open.Span.Start, End: closer.Span.End}, Open: open, Label: label, Close: closer}, true
}

func (p *parser) arrowShape() (*NodeShapeNLabel, bool) {
	open := p.take()
	label, ok := p.expectOrFail("STR")
	if !ok {
		return nil, false
	}
	var dirs []Token
	for p.kind() == "DIR" {
		dirs = append(dirs, p.take())
	}
	if len(dirs) == 0 {
		p.fail("DIR")
		return nil, false
	}
	closer, ok := p.arrowEnd()
	if !ok {
		return nil, false
	}
	return &NodeShapeNLabel{Span: source.Span{Start: open.Span.Start, End: closer.Span.End}, Open: open, Label: label, Close: closer, Dirs: dirs}, true
}

func (p *parser) arrowEnd() (Token, bool) {
	if p.kind() == "BLOCK_ARROW_END" {
		return p.take(), true
	}
	p.fail("BLOCK_ARROW_END", "DIR")
	return Token{}, false
}

func (p *parser) link() (Link, bool) {
	if p.kind() == "LINK" {
		end := p.take()
		return Link{Span: end.Span, End: end}, true
	}
	start := p.take()
	if _, ok := p.expectOrFail("LINK_LABEL"); !ok {
		return Link{}, false
	}
	text, ok := p.expectOrFail("STR")
	if !ok {
		return Link{}, false
	}
	end, ok := p.expectOrFail("LINK")
	if !ok {
		return Link{}, false
	}
	return Link{Span: source.Span{Start: start.Span.Start, End: end.Span.End}, Start: &start, Label: &text, End: end}, true
}

func (p *parser) blockStatement() *BlockStatement {
	keyword := p.take()
	statement := &BlockStatement{Keyword: keyword}
	if p.depth+1 > maxDepth {
		p.issue(codeNesting, "nesting depth exceeds 64", keyword.Span)
		p.skipComposite()
		return nil
	}
	if keyword.Kind == "id-block" {
		header := p.nodeStatement()
		if header == nil {
			return nil
		}
		statement.Header = header
	}
	p.depth++
	statement.Body = p.document()
	p.depth--
	if p.kind() != "end" {
		p.unterminated(p.openerOf(keyword))
		return nil
	}
	statement.End = p.take()
	statement.Span = source.Span{Start: keyword.Span.Start, End: statement.End.Span.End}
	return statement
}

func (p *parser) openerOf(keyword Token) Token {
	if p.kind() == "UNTERMINATED" {
		return p.token()
	}
	return keyword
}

func (p *parser) skipComposite() {
	level := 1
	for !p.atEnd() {
		switch p.kind() {
		case "BLOCK_DIAGRAM_KEY", "id-block":
			level++
		case "end":
			level--
		}
		p.take()
		if level == 0 {
			return
		}
	}
}

func (p *parser) classDefStatement() *ClassDefStatement {
	keyword := p.take()
	id := p.token()
	if id.Kind != "CLASSDEF_ID" {
		p.fail("CLASSDEF_ID", "DEFAULT")
		return nil
	}
	p.take()
	style, ok := p.expectOrFail("CLASSDEF_STYLEOPTS")
	if !ok {
		return nil
	}
	return &ClassDefStatement{Span: source.Span{Start: keyword.Span.Start, End: style.Span.End}, Keyword: keyword, ID: id, Style: style}
}

func (p *parser) cssClassStatement() *CssClassStatement {
	keyword := p.take()
	ids, ok := p.expectOrFail("CLASSENTITY_IDS")
	if !ok {
		return nil
	}
	class, ok := p.expectOrFail("STYLECLASS")
	if !ok {
		return nil
	}
	return &CssClassStatement{Span: source.Span{Start: keyword.Span.Start, End: class.Span.End}, Keyword: keyword, IDs: ids, Class: class}
}

func (p *parser) styleStatement() *StyleStatement {
	keyword := p.take()
	ids, ok := p.expectOrFail("STYLE_ENTITY_IDS")
	if !ok {
		return nil
	}
	style, ok := p.expectOrFail("STYLE_DEFINITION_DATA")
	if !ok {
		return nil
	}
	return &StyleStatement{Span: source.Span{Start: keyword.Span.Start, End: style.Span.End}, Keyword: keyword, IDs: ids, Style: style}
}
