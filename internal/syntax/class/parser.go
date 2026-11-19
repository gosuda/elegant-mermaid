package class

import (
	"fmt"
	"strings"

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

func Parse(src []byte, removed []source.Span) (*File, []diag.Diagnostic) {
	cleaned := source.Clean(src, removed)
	p := parser{src: src, cleaned: cleaned, tokens: lex(cleaned)}
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

func (p *parser) text(start, end int) string {
	return string(p.cleaned.Slice(source.Span{Start: start, End: end}))
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
	p.issue("class/unexpected-token", fmt.Sprintf("unexpected %s, expected one of: %s", p.text(t.Span.Start, t.Span.End), expected), t.Span)
}

func (p *parser) expect(kind, expected string) (Token, bool) {
	t := p.peek()
	if t.Kind == kind {
		p.at++
		return t, true
	}
	p.unexpected(t, expected)
	if t.Kind == "UNTERMINATED" {
		p.at++
	}
	return t, false
}

func (p *parser) recover() {
	for !p.end() && p.peek().Kind != "NEWLINE" && p.peek().Kind != "}" {
		p.at++
	}
}

const childStatements = "CLASS, NAMESPACE, NOTE, NOTE_FOR"

func childStart(kind string) bool {
	return kind == "class" || kind == "namespace" || kind == "note"
}

func (p *parser) statements(depth int) Statements {
	var out Statements
	for !p.end() && p.peek().Kind != "}" {
		if p.accept("NEWLINE") {
			continue
		}
		if depth > 0 && !childStart(p.peek().Kind) {
			p.unexpected(p.peek(), childStatements)
			p.recover()
			continue
		}
		before, diagnostics := p.at, len(p.diags)
		s, ok := p.statement(depth)
		if len(p.diags) != diagnostics {
			if ok {
				out = append(out, s)
			}
			p.recover()
			continue
		}
		if p.at == before {
			p.at++
		}
		p.finishStatement(&s)
		out = append(out, s)
	}
	return out
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

func (p *parser) statement(depth int) (Statement, bool) {
	t := p.peek()
	s := Statement{Kind: t.Kind, Span: t.Span}
	var ok bool
	switch t.Kind {
	case "class":
		s.Class, ok = p.class()
	case "namespace":
		s.Namespace, ok = p.namespace(depth)
	case "note":
		s.Note, ok = p.note()
	case "<<":
		s.Annotation, ok = p.annotation()
	case "ALPHA", "BQUOTE_STR", "-", "UNICODE_TEXT":
		return p.named()
	default:
		ok = p.otherStatement(&s)
	}
	return s, ok
}

func (p *parser) otherStatement(s *Statement) bool {
	ok := true
	switch s.Kind {
	case "style", "cssClass", "classDef":
		s.Style, ok = p.style()
	case "click", "link", "callback":
		s.Click, ok = p.click()
	case "direction_tb", "direction_bt", "direction_rl", "direction_lr":
		token := p.take()
		s.Kind = "direction"
		s.Value = strings.ToUpper(strings.TrimPrefix(token.Kind, "direction_"))
	case "accTitle":
		p.take()
		p.accept(":")
		s.Value = p.lineText()
	case "accDescr":
		s.Value, ok = p.description()
	case "UNTERMINATED":
		p.unexpected(p.take(), "statement")
		ok = false
	default:
		t := p.take()
		p.recover()
		span := t.Span
		span.End = p.tokens[p.at-1].Span.End
		p.issue("class/unknown-statement", "unknown statement "+t.Text, span)
		ok = false
	}
	return ok
}

func nameToken(t Token) bool {
	return t.Kind == "ALPHA" || t.Kind == "BQUOTE_STR" || t.Kind == "-" || t.Kind == "." || t.Kind == "UNICODE_TEXT"
}

func (p *parser) name() (ClassName, bool) {
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
		return n, false
	}
	if p.peek().Kind == "GENERICTYPE" {
		t := p.take()
		n.Generic, n.Span.End = t.Text, t.Span.End
	}
	if p.peek().Kind == "UNTERMINATED" {
		p.unexpected(p.take(), "")
		return n, false
	}
	return n, true
}

func (p *parser) identifier() (ClassIdentifier, bool) {
	start := p.take().Span.Start
	n, ok := p.name()
	id := ClassIdentifier{Name: n, Span: source.Span{Start: start, End: n.Span.End}}
	if !ok || !p.accept("[") {
		return id, ok
	}
	id.HasLabel = true
	label, ok := p.expect("STR", "STR")
	if !ok {
		return id, false
	}
	id.Label = label.Text
	if _, ok := p.expect("]", "SQE"); !ok {
		return id, false
	}
	id.Span.End = p.tokens[p.at-1].Span.End
	return id, true
}

func (p *parser) class() (*ClassStatement, bool) {
	id, ok := p.identifier()
	c := &ClassStatement{Identifier: id, Span: id.Span}
	if !ok {
		return c, false
	}
	if p.accept(":::") {
		c.CSS = p.take().Text
	}
	if p.accept("<<") {
		c.Annotation = p.take().Text
		if _, ok := p.expect(">>", "ANNOTATION_END"); !ok {
			return c, false
		}
	}
	if p.accept("{") {
		c.HasBody = true
		if !p.members(c) {
			return c, false
		}
		if c.CSS != "" && len(c.Members.Tokens) == 0 {
			p.unexpected(p.peek(), "MEMBER")
			return c, false
		}
	}
	c.Span.End = p.tokens[p.at-1].Span.End
	return c, true
}

func (p *parser) members(c *ClassStatement) bool {
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
		return false
	}
	if len(c.Members.Tokens) > 0 {
		c.Members.Span = source.Span{Start: c.Members.Tokens[0].Span.Start, End: c.Members.Tokens[len(c.Members.Tokens)-1].Span.End}
	}
	return true
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

func (p *parser) namespace(depth int) (*NamespaceStatement, bool) {
	id, ok := p.identifier()
	n := &NamespaceStatement{Identifier: id, Span: id.Span}
	if !ok {
		return n, false
	}
	if depth >= 64 {
		p.issue("limit/nesting-depth", "nesting depth exceeds 64", id.Span)
		p.recover()
		return n, false
	}
	if _, ok := p.expect("{", "STRUCT_START"); !ok {
		return n, false
	}
	open := p.tokens[p.at-1].Span.Start
	n.Children = p.statements(depth + 1)
	if len(n.Children) == 0 {
		p.unexpected(p.peek(), childStatements)
	}
	if !p.accept("}") {
		p.issue("class/unterminated", "unterminated {", source.Span{Start: open, End: len(p.src)})
	} else {
		n.Span.End = p.tokens[p.at-1].Span.End
	}
	return n, true
}

func (p *parser) lineText() string {
	start := p.peek().Span.Start
	end := start
	for !p.end() && p.peek().Kind != "NEWLINE" {
		end = p.take().Span.End
	}
	return strings.TrimSpace(p.text(start, end))
}

func (p *parser) description() (string, bool) {
	p.take()
	if !p.accept("{") {
		p.accept(":")
		return p.lineText(), true
	}
	open := p.tokens[p.at-1].Span.Start
	start := p.peek().Span.Start
	for !p.end() && p.peek().Kind != "}" {
		p.take()
	}
	end := p.peek().Span.Start
	if !p.accept("}") {
		p.issue("class/unterminated", "unterminated {", source.Span{Start: open, End: len(p.src)})
		return "", false
	}
	return strings.TrimSpace(p.text(start, end)), true
}
