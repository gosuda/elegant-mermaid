package mindmap

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "mindmap/unexpected-token"
	codeUnknown      = "mindmap/unknown-statement"
	codeUnterminated = "mindmap/unterminated"
)

var (
	startTokens     = []string{kindMindmap, kindSpaceLine}
	statementTokens = []string{kindClass, kindIcon, kindNodeStart, kindNodeID, kindSpaceLine, kindSpaceList}
	stopTokens      = []string{kindEOF, kindNL, kindSpaceLine}
	indentedTokens  = []string{kindClass, kindEOF, kindIcon, kindNL, kindNodeStart, kindNodeID, kindSpaceLine}
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, scan: newScanner(text, removed)}
	p.advance()
	return p.start(), p.diags
}

type parser struct {
	src    string
	scan   *scanner
	tok    Token
	diags  []diag.Diagnostic
	halted bool
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

func (p *parser) advance() {
	p.tok = p.scan.next()
	if p.tok.Kind != kindUnterminated {
		return
	}
	p.diags = append(p.diags, Diagnostic(codeUnterminated, "unterminated "+p.tok.Text, p.tok.Span))
	p.halted = true
	p.tok = Token{Kind: kindEnd, Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) take() Token {
	token := p.tok
	p.advance()
	return token
}

func (p *parser) describe(token Token) string {
	if token.Span.Start == token.Span.End {
		return "end of input"
	}
	return p.src[token.Span.Start:token.Span.End]
}

func (p *parser) unexpected(expected []string) {
	if p.halted {
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	message := "unexpected " + p.describe(p.tok) + ", expected one of: " + strings.Join(names, ", ")
	p.diags = append(p.diags, Diagnostic(codeUnexpected, message, p.tok.Span))
}

func endsLine(token Token) bool {
	switch token.Kind {
	case kindNL, kindEOF:
		return true
	case kindSpaceLine:
		return strings.HasSuffix(token.Text, "\n") || strings.HasSuffix(token.Text, "\r")
	}
	return false
}

func (p *parser) recover(contentEnd int) int {
	token := p.tok
	if !isSeparator(token.Kind) {
		contentEnd = max(contentEnd, token.Span.End)
	}
	if token.Kind == kindEnd {
		return contentEnd
	}
	if !endsLine(token) {
		contentEnd = p.scan.skipLine(contentEnd)
	}
	p.advance()
	if p.tok.Kind == kindEOF {
		p.advance()
	}
	return contentEnd
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.tok.Kind == kind {
		return p.take(), true
	}
	p.unexpected([]string{kind})
	p.recover(p.tok.Span.Start)
	return Token{}, false
}

func (p *parser) start() *Start {
	start := &Start{}
	if p.tok.Kind == kindSpaceLine {
		start.Leading = p.spaceLines()
	}
	if p.tok.Kind != kindMindmap {
		p.unexpected(startTokens)
		start.Span = source.Span{Start: p.tok.Span.Start, End: len(p.src)}
		return start
	}
	start.Header = p.take()
	if p.tok.Kind == kindNL {
		p.advance()
	}
	start.Document = p.document()
	start.Span = source.Span{Start: start.Header.Span.Start, End: max(start.Document.Span.End, start.Header.Span.End)}
	if len(start.Leading) > 0 {
		start.Span.Start = start.Leading[0].Span.Start
	}
	return start
}

func (p *parser) spaceLines() []Token {
	var tokens []Token
	for p.tok.Kind == kindSpaceLine || len(tokens) > 0 && p.tok.Kind == kindNL {
		tokens = append(tokens, p.take())
	}
	return tokens
}

func (p *parser) document() Document {
	doc := Document{Span: source.Span{Start: p.tok.Span.Start, End: p.tok.Span.Start}}
	for p.tok.Kind != kindEnd {
		statement, ok := p.statement()
		if !ok {
			continue
		}
		stop, _ := p.stop()
		doc.Items = append(doc.Items, Item{Statement: statement, Stop: stop})
		doc.Span.End = max(statement.Span.End, stop.Span.End)
	}
	return doc
}

func (p *parser) statement() (Statement, bool) {
	switch p.tok.Kind {
	case kindSpaceLine:
		blank := p.take()
		return Statement{Span: blank.Span, Blank: &blank}, true
	case kindSpaceList:
		indent := p.take()
		return p.indented(indent)
	case kindNodeID, kindNodeStart:
		return p.nodeStatement(nil)
	case kindIcon, kindClass:
		return p.decoration(nil), true
	}
	p.unknownStatement()
	return Statement{}, false
}

func (p *parser) indented(indent Token) (Statement, bool) {
	switch p.tok.Kind {
	case kindNodeID, kindNodeStart:
		return p.nodeStatement(&indent)
	case kindIcon, kindClass:
		return p.decoration(&indent), true
	case kindNL, kindEOF, kindSpaceLine:
		return Statement{Span: indent.Span, Indent: &indent}, true
	}
	p.unexpected(indentedTokens)
	p.recover(indent.Span.End)
	return Statement{}, false
}

func (p *parser) nodeStatement(indent *Token) (Statement, bool) {
	node, ok := p.node()
	if !ok {
		return Statement{}, false
	}
	span := node.Span
	if indent != nil {
		span.Start = indent.Span.Start
	}
	return Statement{Span: span, Indent: indent, Node: node}, true
}

func (p *parser) decoration(indent *Token) Statement {
	token := p.take()
	statement := Statement{Span: token.Span, Indent: indent}
	if indent != nil {
		statement.Span.Start = indent.Span.Start
	}
	if token.Kind == kindIcon {
		statement.Icon = &token
	} else {
		statement.Class = &token
	}
	return statement
}

func (p *parser) node() (*Node, bool) {
	node := &Node{}
	if p.tok.Kind == kindNodeID {
		id := p.take()
		node.ID = &id
		node.Span = id.Span
		if p.tok.Kind != kindNodeStart {
			return node, true
		}
	}
	open := p.take()
	node.Open = &open
	if node.ID == nil {
		node.Span = open.Span
	}
	descr, ok := p.expect(kindNodeDescr)
	if !ok {
		return nil, false
	}
	node.Descr, node.Description = &descr, descr.Quote
	closing, ok := p.expect(kindNodeEnd)
	if !ok {
		return nil, false
	}
	node.Close = &closing
	node.Span.End = closing.Span.End
	return node, true
}

func (p *parser) stop() (Stop, bool) {
	switch p.tok.Kind {
	case kindNL, kindEOF, kindSpaceLine:
	default:
		p.unexpected(stopTokens)
		p.recover(p.tok.Span.Start)
		return Stop{}, false
	}
	first := p.take()
	stop := Stop{Span: first.Span, Tokens: []Token{first}}
	for p.tok.Kind == kindNL || p.tok.Kind == kindEOF {
		token := p.take()
		stop.Tokens = append(stop.Tokens, token)
		stop.Span.End = token.Span.End
	}
	return stop, true
}

func (p *parser) unknownStatement() {
	first := p.tok
	if first.Kind == kindNL || first.Kind == kindEOF {
		p.unexpected(statementTokens)
		p.recover(first.Span.Start)
		return
	}
	end := p.recover(first.Span.End)
	p.diags = append(p.diags, Diagnostic(codeUnknown, "unknown statement "+p.describe(first), source.Span{Start: first.Span.Start, End: end}))
}
