package er

import (
	"fmt"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	cleaned := source.Clean(src, removed)
	p := &parser{src: src, cleaned: cleaned, tokens: lex(cleaned)}
	for p.kind() == "NEWLINE" {
		p.at++
	}
	header, ok := p.expect("ER_DIAGRAM")
	if !ok {
		header = Token{Kind: "ER_DIAGRAM", Span: source.Span{}}
	}
	document := p.document(0, header.Span.End)
	return &Start{
		Span:     source.Span{Start: header.Span.Start, End: len(src)},
		Header:   header,
		Document: document,
	}, p.diags
}

type parser struct {
	src     []byte
	cleaned *source.Cleaned
	tokens  []Token
	at      int
	diags   []diag.Diagnostic
}

func (p *parser) token() Token {
	if p.at < len(p.tokens) {
		return p.tokens[p.at]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) kind() string {
	if p.at < len(p.tokens) {
		return p.tokens[p.at].Kind
	}
	return "EOF"
}

func (p *parser) take() Token {
	t := p.token()
	if p.at < len(p.tokens) {
		p.at++
	}
	return t
}

func (p *parser) end() int {
	if p.at == 0 {
		return 0
	}
	return p.tokens[p.at-1].Span.End
}

func (p *parser) span(start int) source.Span {
	end := p.end()
	if end < start {
		end = start
	}
	return source.Span{Start: start, End: end}
}

func (p *parser) raw(span source.Span) string {
	if span.Start < 0 || span.End > len(p.src) || span.Start > span.End {
		return ""
	}
	return string(p.cleaned.Slice(span))
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span})
}

func (p *parser) unexpected(expected string) {
	t := p.token()
	p.issue("er/unexpected-token", fmt.Sprintf("unexpected %s, expected one of: %s", p.raw(t.Span), expected), t.Span)
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take(), true
	}
	p.failed(kind)
	return Token{}, false
}

func (p *parser) failed(expected string) {
	if p.kind() == "UNTERMINATED" {
		t := p.take()
		p.unterminated(t.Text, t.Span.Start)
		return
	}
	p.unexpected(expected)
}

func (p *parser) unterminated(opener string, start int) {
	if n := len(p.diags); n > 0 {
		last := p.diags[n-1].Code
		if last == "er/unterminated" || last == "limit/nesting-depth" {
			return
		}
	}
	p.issue("er/unterminated", "unterminated "+opener, source.Span{Start: start, End: len(p.src)})
}

func (p *parser) documentDone(depth int) bool {
	return p.kind() == "EOF" || depth > 0 && p.kind() == "END"
}

func (p *parser) document(depth int, start int) Document {
	var lines []Line
	for !p.documentDone(depth) {
		if p.kind() == "NEWLINE" {
			t := p.take()
			lines = append(lines, Line{Span: t.Span})
			continue
		}
		before := p.at
		if s := p.statement(depth); s != nil {
			lines = append(lines, Line{Span: s.Span, Statement: s})
		} else {
			p.recover("END")
			if p.kind() == "SEMI" {
				p.take()
			}
		}
		if p.at == before {
			p.take()
		}
	}
	first, last := start, start
	if len(lines) > 0 {
		first, last = lines[0].Span.Start, lines[len(lines)-1].Span.End
	}
	return Document{Span: source.Span{Start: first, End: last}, Lines: lines}
}

func (p *parser) recover(close string) {
	end := p.token().Span.Start
	for !p.atBoundary(close) {
		t := p.token()
		if strings.ContainsAny(p.raw(source.Span{Start: min(end, len(p.src)), End: t.Span.Start}), "\r\n") {
			return
		}
		if t.Kind == "UNTERMINATED" {
			p.failed("statement")
			continue
		}
		p.take()
		end = p.end()
	}
}

func (p *parser) atBoundary(close string) bool {
	switch p.kind() {
	case "EOF", "NEWLINE", "SEMI", close:
		return true
	}
	return false
}

func (p *parser) statement(depth int) *Statement {
	start := p.token().Span.Start
	var (
		s  *Statement
		ok bool
	)
	switch p.kind() {
	case "ENTITY_NAME", "UNICODE_TEXT", "NUM", "DECIMAL_NUM", "ENTITY_ONE":
		s, ok = p.named()
	case "SUBGRAPH":
		s, ok = p.subgraphStatement(depth)
	case "CLASSDEF", "STYLE", "CLASS":
		s, ok = p.styleStatement()
	case "acc_title", "acc_descr", "acc_descr_multiline_value":
		s, ok = p.accessibilityStatement()
	case "direction_tb", "direction_bt", "direction_rl", "direction_lr":
		s = &Statement{Kind: KindDirection, Direction: p.direction()}
		ok = true
	default:
		if p.kind() == "UNTERMINATED" {
			p.failed("statement")
			return nil
		}
		p.unknown()
		return nil
	}
	if !ok {
		return nil
	}
	if s.Kind == KindClassDef || s.Kind == KindStyle {
		return s
	}
	return p.spanned(start, *s)
}

func (p *parser) spanned(start int, s Statement) *Statement {
	s.Span = p.span(start)
	return &s
}

func (p *parser) unknown() {
	t := p.take()
	p.recover("END")
	p.issue("er/unknown-statement", "unknown statement "+p.raw(t.Span), p.span(t.Span.Start))
}

func entityKind(kind string) bool {
	switch kind {
	case "ENTITY_NAME", "UNICODE_TEXT", "NUM", "DECIMAL_NUM", "ENTITY_ONE":
		return true
	}
	return false
}

func (p *parser) entityName() (EntityName, bool) {
	if !entityKind(p.kind()) {
		p.failed("DECIMAL_NUM, ENTITY_NAME, ENTITY_ONE, NUM, UNICODE_TEXT")
		return EntityName{}, false
	}
	t := p.take()
	return EntityName{Span: t.Span, Name: t.Text}, true
}

func (p *parser) inlineClasses() (*IdList, bool) {
	if p.kind() != "STYLE_SEPARATOR" {
		return nil, true
	}
	p.take()
	list, ok := p.idList()
	if !ok {
		return nil, false
	}
	return list, true
}

func (p *parser) named() (*Statement, bool) {
	name, ok := p.entityName()
	if !ok {
		return nil, false
	}
	alias, ok := p.alias()
	if !ok {
		return nil, false
	}
	classes, ok := p.inlineClasses()
	if !ok {
		return nil, false
	}
	if isCardinality(p.kind()) {
		if alias != nil {
			p.unexpected("BLOCK_START, NEWLINE")
			return nil, false
		}
		relationship, ok := p.relationship(name, classes)
		if !ok {
			return nil, false
		}
		return &Statement{Kind: KindRelationship, Relationship: relationship}, true
	}
	var attributes *Attributes
	var delimiters *[2]source.Span
	if p.kind() == "BLOCK_START" {
		parsed, delims, ok := p.attributes()
		if !ok {
			return nil, false
		}
		attributes, delimiters = parsed, delims
	}
	return &Statement{Kind: KindEntity, Entity: &EntityStatement{Name: name, Alias: alias, Classes: classes, Attributes: attributes, Delimiters: delimiters}}, true
}

func (p *parser) alias() (*EntityName, bool) {
	if p.kind() != "SQS" {
		return nil, true
	}
	p.take()
	name, ok := p.entityName()
	if !ok {
		return nil, false
	}
	if _, ok := p.expect("SQE"); !ok {
		return nil, false
	}
	return &name, true
}

func (p *parser) relationship(from EntityName, fromClasses *IdList) (*RelationshipStatement, bool) {
	relation, ok := p.relSpec()
	if !ok {
		return nil, false
	}
	to, ok := p.entityName()
	if !ok {
		return nil, false
	}
	toClasses, ok := p.inlineClasses()
	if !ok {
		return nil, false
	}
	if _, ok := p.expect("COLON"); !ok {
		return nil, false
	}
	role, ok := p.role()
	if !ok {
		return nil, false
	}
	return &RelationshipStatement{From: from, FromClasses: fromClasses, Relation: relation, To: to, ToClasses: toClasses, Role: role}, true
}

func (p *parser) relSpec() (RelSpec, bool) {
	left, ok := p.cardinality()
	if !ok {
		return RelSpec{}, false
	}
	if p.kind() != "IDENTIFYING" && p.kind() != "NON_IDENTIFYING" {
		p.failed("IDENTIFYING, NON_IDENTIFYING")
		return RelSpec{}, false
	}
	t := p.take()
	right, ok := p.cardinality()
	if !ok {
		return RelSpec{}, false
	}
	return RelSpec{Span: p.span(left.Span.Start), Left: left, RelType: RelType{Span: t.Span, Identifying: t.Kind == "IDENTIFYING", Token: t}, Right: right}, true
}

func isCardinality(kind string) bool {
	switch kind {
	case "ZERO_OR_ONE", "ZERO_OR_MORE", "ONE_OR_MORE", "ONLY_ONE", "MD_PARENT":
		return true
	}
	return false
}

func cardinalityKind(kind string) CardinalityKind {
	switch kind {
	case "ZERO_OR_MORE":
		return CardZeroOrMore
	case "ONE_OR_MORE":
		return CardOneOrMore
	case "ONLY_ONE":
		return CardOnlyOne
	case "MD_PARENT":
		return CardMdParent
	}
	return CardZeroOrOne
}

func (p *parser) cardinality() (Cardinality, bool) {
	if !isCardinality(p.kind()) {
		p.failed("MD_PARENT, ONE_OR_MORE, ONLY_ONE, ZERO_OR_MORE, ZERO_OR_ONE")
		return Cardinality{}, false
	}
	t := p.take()
	return Cardinality{Span: t.Span, Kind: cardinalityKind(t.Kind), Token: t}, true
}

func (p *parser) role() (Role, bool) {
	switch p.kind() {
	case "WORD", "ENTITY_NAME", "UNICODE_TEXT":
		t := p.take()
		return Role{Span: t.Span, Label: t.Text, Token: t}, true
	}
	p.failed("ENTITY_NAME, UNICODE_TEXT, WORD")
	return Role{}, false
}

func (p *parser) attributes() (*Attributes, *[2]source.Span, bool) {
	open := p.take()
	start := p.token().Span.Start
	var list []Attribute
	for p.kind() != "BLOCK_STOP" && p.kind() != "EOF" {
		before := p.at
		if a, ok := p.attribute(); ok {
			list = append(list, a)
		} else {
			p.recover("BLOCK_STOP")
		}
		if p.at == before && p.kind() != "BLOCK_STOP" {
			p.take()
		}
	}
	if p.kind() == "EOF" {
		p.unterminated("{", open.Span.Start)
		return nil, nil, false
	}
	first, last := start, start
	if len(list) > 0 {
		first, last = list[0].Span.Start, list[len(list)-1].Span.End
	}
	close := p.take()
	return &Attributes{Span: source.Span{Start: first, End: last}, Attributes: list}, &[2]source.Span{open.Span, close.Span}, true
}

func (p *parser) attribute() (Attribute, bool) {
	word, ok := p.expect("ATTRIBUTE_WORD")
	if !ok {
		return Attribute{}, false
	}
	start := word.Span.Start
	var question *Token
	if p.kind() == "?" {
		t := p.take()
		question = &t
	}
	typeSpan := p.span(start)
	nameWord, ok := p.expect("ATTRIBUTE_WORD")
	if !ok {
		return Attribute{}, false
	}
	var keys *AttributeKeyTypeList
	if p.kind() == "ATTRIBUTE_KEY" {
		parsed, ok := p.attributeKeys()
		if !ok {
			return Attribute{}, false
		}
		keys = parsed
	}
	var comment *AttributeComment
	if p.kind() == "COMMENT" {
		t := p.take()
		comment = &AttributeComment{Span: t.Span, Text: t.Text}
	}
	return Attribute{
		Span:          p.span(start),
		AttributeType: AttributeType{Span: typeSpan, Word: word, Question: question},
		Name:          AttributeName{Span: nameWord.Span, Word: nameWord},
		Keys:          keys,
		Comment:       comment,
	}, true
}

func (p *parser) attributeKeys() (*AttributeKeyTypeList, bool) {
	start := p.token().Span.Start
	first, ok := p.attributeKey()
	if !ok {
		return nil, false
	}
	keys := []AttributeKeyType{first}
	for p.kind() == "," {
		p.take()
		next, ok := p.attributeKey()
		if !ok {
			return nil, false
		}
		keys = append(keys, next)
	}
	return &AttributeKeyTypeList{Span: p.span(start), Keys: keys}, true
}

func (p *parser) attributeKey() (AttributeKeyType, bool) {
	t, ok := p.expect("ATTRIBUTE_KEY")
	if !ok {
		return AttributeKeyType{}, false
	}
	value := "UK"
	switch {
	case strings.EqualFold(t.Text, "PK"):
		value = "PK"
	case strings.EqualFold(t.Text, "FK"):
		value = "FK"
	}
	return AttributeKeyType{Span: t.Span, Token: t, Value: value}, true
}

func (p *parser) idList() (*IdList, bool) {
	start := p.token().Span.Start
	first, ok := p.id()
	if !ok {
		return nil, false
	}
	names := []Token{first}
	for p.kind() == "COMMA" {
		p.take()
		next, ok := p.id()
		if !ok {
			return nil, false
		}
		names = append(names, next)
	}
	return &IdList{Span: p.span(start), Names: names}, true
}

func (p *parser) id() (Token, bool) {
	if p.kind() == "STYLE_TEXT" || p.kind() == "UNICODE_TEXT" {
		return p.take(), true
	}
	p.failed("STYLE_TEXT, UNICODE_TEXT")
	return Token{}, false
}

func (p *parser) styles() (*StylesOpt, bool) {
	start := p.token().Span.Start
	first, ok := p.style()
	if !ok {
		return nil, false
	}
	list := []Style{first}
	for p.kind() == "COMMA" {
		p.take()
		next, ok := p.style()
		if !ok {
			return nil, false
		}
		list = append(list, next)
	}
	return &StylesOpt{Span: p.span(start), Styles: list}, true
}

func (p *parser) style() (Style, bool) {
	start := p.token().Span.Start
	var components []Token
	for {
		switch p.kind() {
		case "STYLE_TEXT", "NUM", "COLON", "BRKT":
			components = append(components, p.take())
			continue
		}
		break
	}
	if len(components) == 0 {
		p.failed("BRKT, COLON, NUM, STYLE_TEXT")
		return Style{}, false
	}
	return Style{Span: p.span(start), Components: components}, true
}

func (p *parser) styleStatement() (*Statement, bool) {
	t := p.take()
	targets, ok := p.idList()
	if !ok {
		return nil, false
	}
	if t.Kind == "CLASS" {
		classes, ok := p.idList()
		if !ok {
			return nil, false
		}
		return &Statement{Kind: KindClass, Span: p.span(t.Span.Start), Class: &ClassStatement{Span: p.span(t.Span.Start), Targets: *targets, Classes: *classes}}, true
	}
	styles, ok := p.styles()
	if !ok {
		return nil, false
	}
	span := p.span(t.Span.Start)
	if _, ok := p.separator(); !ok {
		return nil, false
	}
	if t.Kind == "CLASSDEF" {
		return &Statement{Kind: KindClassDef, Span: span, ClassDef: &ClassDefStatement{Span: span, IDs: *targets, Styles: *styles}}, true
	}
	return &Statement{Kind: KindStyle, Span: span, Style: &StyleStatement{Span: span, Targets: *targets, Styles: *styles}}, true
}

func (p *parser) separator() (Token, bool) {
	switch p.kind() {
	case "SEMI", "NEWLINE", "EOF":
		return p.take(), true
	}
	p.failed("EOF, NEWLINE, SEMI")
	return Token{}, false
}

func (p *parser) accessibilityStatement() (*Statement, bool) {
	t := p.take()
	if t.Kind == "acc_descr_multiline_value" {
		return &Statement{Kind: KindAccessibility, Accessibility: AccessibilityStatement{Value: t}}, true
	}
	title := t.Kind == "acc_title"
	expected := "acc_descr_value"
	if title {
		expected = "acc_title_value"
	}
	value, ok := p.expect(expected)
	if !ok {
		return nil, false
	}
	return &Statement{Kind: KindAccessibility, Accessibility: AccessibilityStatement{Title: title, Value: value}}, true
}

func (p *parser) direction() Direction {
	t := p.take()
	value := "LR"
	switch t.Kind {
	case "direction_tb":
		value = "TB"
	case "direction_bt":
		value = "BT"
	case "direction_rl":
		value = "RL"
	}
	return Direction{Span: t.Span, Value: value}
}

func (p *parser) subgraphStatement(depth int) (*Statement, bool) {
	open := p.take()
	if depth >= 64 {
		p.issue("limit/nesting-depth", "nesting depth exceeds 64", open.Span)
		p.at = len(p.tokens)
		return nil, false
	}
	id, ok := p.entityName()
	if !ok {
		return nil, false
	}
	title, ok := p.subgraphTitle()
	if !ok {
		return nil, false
	}
	header := SubgraphHeader{Span: p.span(open.Span.Start), ID: id, Title: title}
	if _, ok := p.separator(); !ok {
		return nil, false
	}
	document := p.document(depth+1, p.end())
	if p.kind() == "EOF" {
		p.unterminated("subgraph", open.Span.Start)
		return nil, false
	}
	close, ok := p.expect("END")
	if !ok {
		return nil, false
	}
	return &Statement{Kind: KindSubgraph, Subgraph: &SubgraphStatement{Header: header, Document: document, Close: close}}, true
}

func (p *parser) subgraphTitle() (*SubgraphTitle, bool) {
	if p.kind() != "SQS" {
		return nil, true
	}
	p.take()
	first, ok := p.entityName()
	if !ok {
		return nil, false
	}
	parts := []EntityName{first}
	for entityKind(p.kind()) {
		next, ok := p.entityName()
		if !ok {
			return nil, false
		}
		parts = append(parts, next)
	}
	if _, ok := p.expect("SQE"); !ok {
		return nil, false
	}
	return &SubgraphTitle{Span: p.span(parts[0].Span.Start), Parts: parts}, true
}
