package venn

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeUnexpected   = "venn/unexpected-token"
	codeUnknown      = "venn/unknown-statement"
	codeUnterminated = "venn/unterminated"
)

var (
	identifierKinds = []string{"IDENTIFIER", "STRING"}
	textIDKinds     = []string{"IDENTIFIER", "NUMERIC", "STRING"}
	listFollowKinds = []string{"COMMA", "IDENTIFIER", "NUMERIC", "STRING"}
	styleKeyKinds   = []string{"COMMA", "IDENTIFIER"}
	valueKinds      = []string{"HEXCOLOR", "IDENTIFIER", "NUMERIC", "RGBACOLOR", "RGBCOLOR"}
	styleValueKinds = []string{"HEXCOLOR", "IDENTIFIER", "NUMERIC", "RGBACOLOR", "RGBCOLOR", "STRING"}
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	p := &parser{src: text, lx: newLexer(text, removed)}
	p.cur = p.lx.next()
	start := p.start()
	return start, p.diags
}

type parser struct {
	src     string
	lx      *lexer
	cur     Token
	prevEnd int
	diags   []diag.Diagnostic
}

func (p *parser) kind() string { return p.cur.Kind }

func (p *parser) take() Token {
	t := p.cur
	p.prevEnd = t.Span.End
	if t.Kind != "EOF" {
		p.cur = p.lx.next()
	}
	return t
}

func (p *parser) raw(span source.Span) string { return sub(p.src, span.Start, span.End) }

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

func (p *parser) unexpected(expected ...string) {
	if p.kind() == "UNTERMINATED" {
		p.unterminated()
		return
	}
	names := slices.Clone(expected)
	slices.Sort(names)
	found := "end of input"
	if p.kind() != "EOF" {
		found = p.raw(p.cur.Span)
	}
	p.issue(codeUnexpected, "unexpected "+found+", expected one of: "+strings.Join(names, ", "), p.cur.Span)
	p.recover()
}

func (p *parser) unterminated() {
	t := p.take()
	p.issue(codeUnterminated, "unterminated "+t.Text, t.Span)
}

func (p *parser) atBoundary() bool {
	switch p.kind() {
	case "NEWLINE", "EOF", "UNTERMINATED":
		return true
	}
	return false
}

func (p *parser) recover() {
	for !p.atBoundary() {
		p.take()
	}
}

func (p *parser) start() *Start {
	s := &Start{Span: source.Span{Start: p.cur.Span.Start}}
	s.Leading.Span.Start = p.cur.Span.Start
	for p.kind() == "NEWLINE" {
		t := p.take()
		s.Leading.Newlines = append(s.Leading.Newlines, t)
		s.Leading.Span.End = t.Span.End
	}
	if p.kind() == "VENN" {
		s.Header = p.take()
	} else {
		p.unexpected("VENN")
	}
	s.Document = p.document()
	s.Span.End = len(p.src)
	return s
}

func (p *parser) document() Document {
	d := Document{Span: source.Span{Start: p.cur.Span.Start, End: p.cur.Span.Start}}
	for p.kind() != "EOF" {
		line, ok := p.line()
		if !ok {
			continue
		}
		d.Lines = append(d.Lines, line)
		d.Span.End = max(d.Span.End, line.Span.End)
	}
	return d
}

func (p *parser) line() (Line, bool) {
	switch p.kind() {
	case "NEWLINE":
		t := p.take()
		return Line{Span: t.Span, Newline: &t}, true
	case "UNTERMINATED":
		p.unterminated()
		return Line{}, false
	}
	if !startsStatement(p.kind()) {
		p.unknownStatement()
		return Line{}, false
	}
	kind := p.statement()
	if kind == nil {
		return Line{}, false
	}
	span := statementSpan(kind)
	return Line{Span: span, Statement: &Statement{Span: span, Kind: kind}}, true
}

func startsStatement(kind string) bool {
	switch kind {
	case "TITLE", "SET", "UNION", "TEXT", "INDENT_TEXT", "STYLE":
		return true
	}
	return false
}

func statementSpan(kind StatementKind) source.Span {
	switch k := kind.(type) {
	case *Title:
		return k.Span
	case *Set:
		return k.Span
	case *Union:
		return k.Span
	case *Text:
		return k.Span
	case *IndentedText:
		return k.Span
	case *Style:
		return k.Span
	}
	return source.Span{}
}

func (p *parser) unknownStatement() {
	first := p.take()
	end := first.Span.End
	for !p.atBoundary() {
		end = p.take().Span.End
	}
	p.issue(codeUnknown, "unknown statement "+p.raw(first.Span), source.Span{Start: first.Span.Start, End: end})
}

func (p *parser) statement() StatementKind {
	switch p.kind() {
	case "TITLE":
		t := p.take()
		return &Title{Span: t.Span, Token: t}
	case "SET":
		return nonNil(p.set())
	case "UNION":
		return nonNil(p.union())
	case "TEXT":
		return nonNil(p.text())
	case "INDENT_TEXT":
		return nonNil(p.indentedText())
	}
	return nonNil(p.style())
}

func nonNil[P interface {
	StatementKind
	comparable
}](node P) StatementKind {
	var zero P
	if node == zero {
		return nil
	}
	return node
}

func (p *parser) identifier(expected []string) (Identifier, bool) {
	if !slices.Contains(expected, p.kind()) {
		p.unexpected(expected...)
		return Identifier{}, false
	}
	t := p.take()
	return Identifier{Span: t.Span, Kind: t.Kind, Text: t.Text}, true
}

func (p *parser) identifierList() (IdentifierList, bool) {
	first, ok := p.identifier(identifierKinds)
	if !ok {
		return IdentifierList{}, false
	}
	list := IdentifierList{Span: first.Span, IDs: []Identifier{first}}
	for p.kind() == "COMMA" {
		p.take()
		next, ok := p.identifier(identifierKinds)
		if !ok {
			return IdentifierList{}, false
		}
		list.IDs = append(list.IDs, next)
		list.Span.End = next.Span.End
	}
	return list, true
}

func (p *parser) optionalLabel() *Token {
	if p.kind() != "BRACKET_LABEL" {
		return nil
	}
	t := p.take()
	return &t
}

func (p *parser) optionalSize() (*Number, bool) {
	if p.kind() != "COLON" {
		return nil, true
	}
	p.take()
	if p.kind() != "NUMERIC" {
		p.unexpected("NUMERIC")
		return nil, false
	}
	t := p.take()
	return &Number{Span: t.Span, Text: t.Text}, true
}

func (p *parser) set() *Set {
	keyword := p.take()
	id, ok := p.identifier(identifierKinds)
	if !ok {
		return nil
	}
	s := &Set{Keyword: keyword, ID: id, Span: source.Span{Start: keyword.Span.Start, End: id.Span.End}}
	if s.Label = p.optionalLabel(); s.Label != nil {
		s.Span.End = s.Label.Span.End
	}
	size, ok := p.optionalSize()
	if !ok {
		return nil
	}
	if s.Size = size; size != nil {
		s.Span.End = size.Span.End
	}
	p.lx.indent = true
	return s
}

func (p *parser) union() *Union {
	keyword := p.take()
	ids, ok := p.identifierList()
	if !ok {
		return nil
	}
	u := &Union{Keyword: keyword, IDs: ids, Span: source.Span{Start: keyword.Span.Start, End: ids.Span.End}}
	if u.Label = p.optionalLabel(); u.Label != nil {
		u.Span.End = u.Label.Span.End
	}
	size, ok := p.optionalSize()
	if !ok {
		return nil
	}
	if u.Size = size; size != nil {
		u.Span.End = size.Span.End
	}
	p.lx.indent = true
	return u
}

func (p *parser) textID() (Identifier, bool) {
	if !slices.Contains(textIDKinds, p.kind()) {
		p.unexpected(listFollowKinds...)
		return Identifier{}, false
	}
	return p.takeIdentifier(), true
}

func (p *parser) takeIdentifier() Identifier {
	t := p.take()
	return Identifier{Span: t.Span, Kind: t.Kind, Text: t.Text}
}

func (p *parser) text() *Text {
	keyword := p.take()
	targets, ok := p.identifierList()
	if !ok {
		return nil
	}
	id, ok := p.textID()
	if !ok {
		return nil
	}
	t := &Text{Keyword: keyword, Targets: targets, ID: id, Span: source.Span{Start: keyword.Span.Start, End: id.Span.End}}
	if id.Kind != "NUMERIC" {
		if t.Label = p.optionalLabel(); t.Label != nil {
			t.Span.End = t.Label.Span.End
		}
	}
	return t
}

func (p *parser) indentedText() *IndentedText {
	keyword := p.take()
	if !slices.Contains(textIDKinds, p.kind()) {
		p.unexpected(textIDKinds...)
		return nil
	}
	id := p.takeIdentifier()
	tail := IndentedTextTail{Span: id.Span, ID: id}
	if id.Kind != "NUMERIC" {
		if tail.Label = p.optionalLabel(); tail.Label != nil {
			tail.Span.End = tail.Label.Span.End
		}
	}
	return &IndentedText{Keyword: keyword, Tail: tail, Span: source.Span{Start: keyword.Span.Start, End: tail.Span.End}}
}

func (p *parser) style() *Style {
	keyword := p.take()
	targets, ok := p.identifierList()
	if !ok {
		return nil
	}
	if p.kind() != "IDENTIFIER" {
		p.unexpected(styleKeyKinds...)
		return nil
	}
	fields, ok := p.stylesOpt()
	if !ok {
		return nil
	}
	return &Style{Keyword: keyword, Targets: targets, Styles: fields, Span: source.Span{Start: keyword.Span.Start, End: fields.Span.End}}
}

func (p *parser) stylesOpt() (StylesOpt, bool) {
	var out StylesOpt
	for {
		field, ok := p.styleField()
		if !ok {
			return StylesOpt{}, false
		}
		if len(out.Fields) == 0 {
			out.Span.Start = field.Span.Start
		}
		out.Fields = append(out.Fields, field)
		out.Span.End = field.Span.End
		if p.kind() != "COMMA" {
			return out, true
		}
		p.take()
		if p.kind() != "IDENTIFIER" {
			p.unexpected("IDENTIFIER")
			return StylesOpt{}, false
		}
	}
}

func (p *parser) styleField() (StyleField, bool) {
	key := p.take()
	if p.kind() != "COLON" {
		p.unexpected("COLON")
		return StyleField{}, false
	}
	p.take()
	value, ok := p.styleValue()
	if !ok {
		return StyleField{}, false
	}
	return StyleField{Key: key, Value: value, Span: source.Span{Start: key.Span.Start, End: value.Span.End}}, true
}

func (p *parser) styleValue() (StyleValue, bool) {
	switch {
	case p.kind() == "STRING":
		t := p.take()
		return StyleValue{Span: t.Span, String: &t}, true
	case slices.Contains(valueKinds, p.kind()):
		tokens := p.valueTokens()
		return StyleValue{Span: tokens.Span, Tokens: &tokens}, true
	}
	p.unexpected(styleValueKinds...)
	return StyleValue{}, false
}

func (p *parser) valueTokens() ValueTokens {
	out := ValueTokens{Span: source.Span{Start: p.cur.Span.Start}}
	for slices.Contains(valueKinds, p.kind()) {
		t := p.take()
		out.Tokens = append(out.Tokens, ValueToken{Span: t.Span, Kind: t.Kind, Text: t.Text})
		out.Span.End = t.Span.End
	}
	return out
}
