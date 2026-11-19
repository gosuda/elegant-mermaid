package agentflow

func (p *parser) link() *Link {
	start := p.position()
	var id *Token
	if p.kind() == "LINK_ID" {
		id = p.take()
	}
	var opening *Token
	if p.kind() == "START_LINK" {
		opening = p.take()
	}
	var splitLabel *Text
	if opening != nil {
		splitLabel = p.text([]string{"EDGE_TEXT", "UNICODE_TEXT"})
		if splitLabel == nil {
			return nil
		}
	}
	operator := p.require("LINK")
	if operator == nil {
		return nil
	}
	statement := LinkStatement{Span: p.span(start), ID: id, Operator: *operator}
	var arrowText *ArrowText
	if p.kind() == "PIPE" {
		arrowText = p.arrowText()
		if arrowText == nil {
			return nil
		}
	}
	var edgeText *EdgeText
	if splitLabel != nil {
		edgeText = &EdgeText{Span: splitLabel.Span, Text: *splitLabel}
	}
	return &Link{Span: p.span(start), Statement: statement, Opening: opening, ArrowText: arrowText, EdgeText: edgeText}
}

func (p *parser) arrowText() *ArrowText {
	open := p.take()
	if open == nil {
		return nil
	}
	text := p.labelText(open)
	if text == nil {
		return nil
	}
	if p.close(open, "PIPE") == nil {
		return nil
	}
	return &ArrowText{Span: p.span(open.Span.Start), Text: *text}
}

func (p *parser) styleStatement() *StatementKind {
	keyword := p.take()
	if keyword == nil {
		return nil
	}
	if p.requireSpace() == nil {
		return nil
	}
	targets := p.id()
	if targets == nil {
		return nil
	}
	if p.requireSpace() == nil {
		return nil
	}
	spanStart := keyword.Span.Start
	if keyword.Kind == "CLASS" {
		class := p.id()
		if class == nil {
			return nil
		}
		return &StatementKind{Class: &ClassStatement{Span: p.span(spanStart), Targets: *targets, Class: *class}}
	}
	styles := p.styles()
	if styles == nil {
		return nil
	}
	span := p.span(spanStart)
	if keyword.Kind == "CLASSDEF" {
		return &StatementKind{ClassDef: &ClassDefStatement{Span: span, ID: *targets, Styles: *styles}}
	}
	return &StatementKind{Style: &StyleStatement{Span: span, Targets: *targets, Styles: *styles}}
}

func (p *parser) requireSpace() *struct{} {
	if p.spaces() > 0 {
		return &struct{}{}
	}
	p.unexpected("SPACE")
	return nil
}

func (p *parser) styles() *StylesOpt {
	start := p.position()
	first := p.style()
	if first == nil {
		return nil
	}
	styles := []Style{*first}
	for p.kind() == "COMMA" {
		p.at++
		next := p.style()
		if next == nil {
			return nil
		}
		styles = append(styles, *next)
	}
	return &StylesOpt{Span: p.span(start), Styles: styles}
}

func (p *parser) style() *Style {
	start := p.position()
	var components []StyleComponent
	for p.kind() == "NUM" || p.kind() == "NODE_STRING" || p.kind() == "COLON" || p.kind() == "SPACE" || p.kind() == "BRKT" || p.kind() == "STYLE" {
		token := p.take()
		if token == nil {
			return nil
		}
		components = append(components, StyleComponent{Span: token.Span, Token: *token})
	}
	if len(components) == 0 {
		p.unexpected("BRKT, COLON, NODE_STRING, NUM, SPACE, STYLE")
		return nil
	}
	return &Style{Span: p.span(start), Components: components}
}

func (p *parser) linkStyle() *LinkStyleStatement {
	first := p.take()
	if first == nil {
		return nil
	}
	if p.requireSpace() == nil {
		return nil
	}
	def, indices, ok := p.linkStyleTarget()
	if !ok {
		return nil
	}
	if p.requireSpace() == nil {
		return nil
	}
	interpolation, ok := p.interpolationClause()
	if !ok {
		return nil
	}
	p.spaces()
	styles, ok := p.optionalStyles()
	if !ok {
		return nil
	}
	if interpolation == nil && styles == nil {
		p.unexpected("NODE_STRING")
		return nil
	}
	return &LinkStyleStatement{Span: p.span(first.Span.Start), Default: def, Indices: indices, Interpolation: interpolation, Styles: styles}
}

func (p *parser) linkStyleTarget() (*Token, *NumList, bool) {
	if p.kind() == "DEFAULT" {
		return p.take(), nil, true
	}
	indices := p.numList()
	return nil, indices, indices != nil
}

func (p *parser) interpolationClause() (*AlphaNum, bool) {
	if p.kind() != "INTERPOLATE" {
		return nil, true
	}
	p.at++
	if p.requireSpace() == nil {
		return nil, false
	}
	value := p.alphaNum()
	return value, value != nil
}

func (p *parser) optionalStyles() (*StylesOpt, bool) {
	if boundary(p.kind()) {
		return nil, true
	}
	styles := p.styles()
	return styles, styles != nil
}

func (p *parser) numList() *NumList {
	start := p.position()
	first := p.require("NUM")
	if first == nil {
		return nil
	}
	indices := []Token{*first}
	for p.kind() == "COMMA" {
		p.at++
		next := p.require("NUM")
		if next == nil {
			return nil
		}
		indices = append(indices, *next)
	}
	return &NumList{Span: p.span(start), Indices: indices}
}

func (p *parser) alphaNum() *AlphaNum {
	start := p.position()
	var tokens []Token
	for alphaKind(p.kind()) {
		if t := p.take(); t != nil {
			tokens = append(tokens, *t)
		} else {
			return nil
		}
	}
	if len(tokens) == 0 {
		p.unexpected("AMP, BRKT, COLON, COMMA, DIR, DOWN, MINUS, MULT, NODE_STRING, NUM, UNICODE_TEXT")
		return nil
	}
	return &AlphaNum{Span: p.span(start), Tokens: tokens}
}

func (p *parser) click() *ClickStatement {
	id := p.take()
	if id == nil {
		return nil
	}
	start := id.Span.Start
	result := ClickStatement{Span: id.Span, ID: *id}
	if !p.clickAction(&result) {
		return nil
	}
	p.spaces()
	if p.kind() == "STR" {
		result.Tooltip = p.take()
		p.spaces()
	}
	if p.kind() == "LINK_TARGET" {
		result.Target = p.take()
	}
	if result.Callback != nil && result.Target != nil {
		p.unexpected("COMMENT, EOF, NEWLINE, SEMI")
		return nil
	}
	result.Span = p.span(start)
	return &result
}

func (p *parser) clickAction(result *ClickStatement) bool {
	switch p.kind() {
	case "HREF":
		p.at++
		result.URL = p.require("STR")
		return result.URL != nil
	case "STR":
		result.URL = p.take()
		return result.URL != nil
	case "CALLBACKNAME":
		t := p.take()
		if t == nil {
			return false
		}
		result.Callback = &AlphaNum{Span: t.Span, Tokens: []Token{*t}}
		if p.kind() == "CALLBACKARGS" {
			result.Arguments = p.take()
		}
		return true
	default:
		result.Callback = p.alphaNum()
		return result.Callback != nil
	}
}
