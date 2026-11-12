package class

import (
	"fmt"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type parser struct {
	src    []byte
	tokens []Token
	at     int
	diags  []diag.Diagnostic
}

func Parse(src []byte, removed []source.Span) (*File, []diag.Diagnostic) {
	p := parser{src: src, tokens: Lex(src, removed)}
	f := &File{Span: source.Span{End: len(src)}}
	p.newlines()
	f.Header = p.take()
	if f.Header.Kind != "classDiagram" && f.Header.Kind != "classDiagram-v2" {
		p.unexpected(f.Header, "CLASS_DIAGRAM")
	}
	if !p.accept("NEWLINE") {
		p.unexpected(p.peek(), "NEWLINE")
	}
	p.newlines()
	f.Statements = p.statements(0)
	if len(f.Statements) == 0 && len(p.diags) == 0 {
		p.unexpected(p.peek(), "statement")
	}
	if !p.end() {
		p.unexpected(p.peek(), "EOF")
	}
	diag.Sort(p.diags)
	return f, p.diags
}

func (p *parser) end() bool { return p.at >= len(p.tokens) }

func (p *parser) peek() Token {
	if p.end() {
		return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
	}
	return p.tokens[p.at]
}

func (p *parser) take() Token {
	t := p.peek()
	if !p.end() {
		p.at++
	}
	return t
}

func (p *parser) accept(kind string) bool {
	if p.peek().Kind != kind {
		return false
	}
	p.at++
	return true
}

func (p *parser) newlines() {
	for p.accept("NEWLINE") {
	}
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span})
}

func (p *parser) unexpected(t Token, expected string) {
	if t.Kind == "UNTERMINATED" {
		p.issue("class/unterminated", "unterminated "+t.Text, t.Span)
		return
	}
	p.issue("class/unexpected-token", fmt.Sprintf("unexpected %s, expected one of: %s", t.Text, expected), t.Span)
}

func (p *parser) recover() {
	for !p.end() && p.peek().Kind != "NEWLINE" && p.peek().Kind != "}" {
		p.at++
	}
}

func (p *parser) statements(depth int) Statements {
	var out Statements
	for !p.end() && p.peek().Kind != "}" {
		before, diagnostics := p.at, len(p.diags)
		s := p.statement(depth)
		p.finishStatement(&s)
		if !allowedChild(s, depth) {
			p.unexpected(Token{Text: s.Kind, Span: s.Span}, "CLASS, NAMESPACE, NOTE, NOTE_FOR")
		}
		if p.keepStatement(s, diagnostics) {
			out = append(out, s)
		} else {
			p.recover()
		}
		if p.at == before {
			p.at++
		}
		p.newlines()
	}
	return out
}

func allowedChild(s Statement, depth int) bool {
	return depth == 0 || s.Class != nil || s.Namespace != nil || s.Note != nil
}

func (p *parser) keepStatement(s Statement, diagnostics int) bool {
	return len(p.diags) == diagnostics || s.Namespace != nil && s.Namespace.Identifier.Name.Value != ""
}

func (p *parser) finishStatement(s *Statement) {
	if p.peek().Kind != "NEWLINE" && p.peek().Kind != "EOF" && p.peek().Kind != "}" {
		p.unexpected(p.peek(), "NEWLINE")
		p.recover()
	}
	if p.at > 0 {
		s.Span.End = p.tokens[p.at-1].Span.End
	}
	if s.Relation != nil {
		s.Relation.Span = s.Span
	}
	if s.Member != nil {
		s.Member.Span = s.Span
	}
}

func (p *parser) statement(depth int) Statement {
	t := p.peek()
	s := Statement{Kind: t.Kind, Span: t.Span}
	switch t.Kind {
	case "class":
		s.Class = p.class()
	case "namespace":
		s.Namespace = p.namespace(depth)
	case "note":
		s.Note = p.note()
	case "<<":
		s.Annotation = p.annotation()
	case "ALPHA", "BQUOTE_STR", "-", "UNICODE_TEXT":
		return p.named()
	default:
		p.otherStatement(&s)
	}
	return s
}

func (p *parser) otherStatement(s *Statement) {
	switch s.Kind {
	case "style", "cssClass", "classDef":
		s.Style = p.style()
	case "click", "link", "callback":
		s.Click = p.click()
	case "direction_tb", "direction_bt", "direction_rl", "direction_lr":
		token := p.take()
		s.Kind = "direction"
		s.Value = strings.ToUpper(strings.TrimPrefix(token.Kind, "direction_"))
	case "direction", "accTitle":
		p.take()
		p.accept(":")
		s.Value = p.lineText()
	case "accDescr":
		s.Value = p.description()
	case "UNTERMINATED":
		p.unexpected(p.take(), "statement")
	default:
		t := p.take()
		p.recover()
		span := t.Span
		span.End = p.peek().Span.Start
		p.issue("class/unknown-statement", "unknown statement "+t.Text, span)
	}
}

func nameToken(t Token) bool {
	return t.Kind == "ALPHA" || t.Kind == "BQUOTE_STR" || t.Kind == "-" || t.Kind == "." || t.Kind == "UNICODE_TEXT"
}

func (p *parser) name() ClassName {
	n := ClassName{Span: p.peek().Span}
	var value strings.Builder
	for nameToken(p.peek()) {
		t := p.take()
		value.WriteString(t.Text)
		n.Span.End = t.Span.End
	}
	n.Value = value.String()
	if n.Value == "" {
		p.unexpected(p.peek(), "ALPHA, BQUOTE_STR, MINUS, NUM, UNICODE_TEXT")
	}
	if p.peek().Kind == "GENERICTYPE" {
		t := p.take()
		n.Generic, n.Span.End = t.Text, t.Span.End
	}
	return n
}

func (p *parser) identifier() ClassIdentifier {
	start := p.take().Span.Start
	n := p.name()
	id := ClassIdentifier{Name: n, Span: source.Span{Start: start, End: n.Span.End}}
	if p.accept("[") {
		id.HasLabel = true
		t := p.take()
		if t.Kind != "STR" {
			p.unexpected(t, "STR")
		}
		id.Label = t.Text
		if !p.accept("]") {
			p.unexpected(p.peek(), "SQE")
		}
		id.Span.End = p.tokens[p.at-1].Span.End
	}
	return id
}

func (p *parser) class() *ClassStatement {
	id := p.identifier()
	c := &ClassStatement{Identifier: id, Span: id.Span}
	if p.accept(":::") {
		c.CSS = p.take().Text
	}
	if p.accept("<<") {
		c.Annotation = p.take().Text
		if !p.accept(">>") {
			p.unexpected(p.peek(), "ANNOTATION_END")
		}
	}
	if p.accept("{") {
		c.HasBody = true
		p.members(c)
		if c.CSS != "" && len(c.Members.Tokens) == 0 {
			p.unexpected(p.peek(), "MEMBER")
		}
	}
	c.Span.End = p.tokens[p.at-1].Span.End
	return c
}

func (p *parser) members(c *ClassStatement) {
	open := p.tokens[p.at-1].Span.Start
	for !p.end() && p.peek().Kind != "}" {
		t := p.take()
		switch t.Kind {
		case "NEWLINE":
		case "{":
			p.issue("class/nested-member-block", "class member cannot contain a block", t.Span)
			p.skipMemberBlock()
		case "MEMBER":
			c.Members.Tokens = append(c.Members.Tokens, t)
		default:
			p.unexpected(t, "MEMBER, STRUCT_STOP")
		}
	}
	if !p.accept("}") {
		p.issue("class/unterminated", "unterminated {", source.Span{Start: open, End: len(p.src)})
	}
	if len(c.Members.Tokens) > 0 {
		c.Members.Span = source.Span{Start: c.Members.Tokens[0].Span.Start, End: c.Members.Tokens[len(c.Members.Tokens)-1].Span.End}
	}
}

func (p *parser) skipMemberBlock() {
	depth := 1
	for !p.end() && depth > 0 {
		switch p.take().Kind {
		case "{":
			depth++
		case "}":
			depth--
		}
	}
}

func (p *parser) namespace(depth int) *NamespaceStatement {
	id := p.identifier()
	n := &NamespaceStatement{Identifier: id, Span: id.Span}
	if depth >= 64 {
		p.issue("limit/nesting-depth", "nesting depth exceeds 64", id.Span)
		p.recover()
		return n
	}
	if !p.accept("{") {
		p.unexpected(p.peek(), "STRUCT_START")
		return n
	}
	open := p.tokens[p.at-1].Span.Start
	p.newlines()
	n.Children = p.statements(depth + 1)
	if len(n.Children) == 0 {
		p.unexpected(p.peek(), "CLASS, NAMESPACE, NOTE, NOTE_FOR")
	}
	if !p.accept("}") {
		p.issue("class/unterminated", "unterminated {", source.Span{Start: open, End: len(p.src)})
	} else {
		n.Span.End = p.tokens[p.at-1].Span.End
	}
	return n
}

func (p *parser) lineText() string {
	start := p.peek().Span.Start
	end := start
	for !p.end() && p.peek().Kind != "NEWLINE" {
		end = p.take().Span.End
	}
	return strings.TrimSpace(string(p.src[start:end]))
}

func (p *parser) description() string {
	p.take()
	if !p.accept("{") {
		p.accept(":")
		return p.lineText()
	}
	open := p.tokens[p.at-1].Span.Start
	start := p.peek().Span.Start
	for !p.end() && p.peek().Kind != "}" {
		p.take()
	}
	end := p.peek().Span.Start
	if !p.accept("}") {
		p.issue("class/unterminated", "unterminated {", source.Span{Start: open, End: len(p.src)})
	}
	return strings.TrimSpace(string(p.src[start:end]))
}
