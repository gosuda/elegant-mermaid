package railroad

import "github.com/gosuda/elegant-mermaid/internal/source"

var constructorStarts = []string{"choice", "nonterminal", "oneOrMore", "optional", "sequence", "special", "terminal", "zeroOrMore"}

func (p *parser) railroadExpr() (Expression, bool) {
	t := p.tok()
	switch t.Kind {
	case "sequence", "choice":
		return p.railroadList(t)
	case "optional", "oneOrMore", "zeroOrMore":
		return p.railroadUnary(t)
	case "terminal", "nonterminal", "special":
		return p.railroadLeaf(t)
	}
	p.fail(constructorStarts...)
	return nil, false
}

func (p *parser) railroadList(keyword Token) (Expression, bool) {
	p.take()
	open, ok := p.expect("(")
	if !ok || !p.enter(open) {
		return nil, false
	}
	var items []Expression
	for {
		item, ok := p.railroadExpr()
		if !ok {
			return nil, false
		}
		items = append(items, item)
		if p.kind() != "," {
			break
		}
		p.take()
	}
	if _, ok := p.expect(")", ")", ","); !ok {
		return nil, false
	}
	p.depth--
	span := p.since(keyword.Span.Start)
	if keyword.Kind == "sequence" {
		return &RailroadSequenceExpr{Span: span, Elements: items}, true
	}
	return &RailroadChoiceExpr{Span: span, Alternatives: items}, true
}

func (p *parser) railroadUnary(keyword Token) (Expression, bool) {
	p.take()
	open, ok := p.expect("(")
	if !ok || !p.enter(open) {
		return nil, false
	}
	item, ok := p.railroadExpr()
	if !ok {
		return nil, false
	}
	if _, ok := p.expect(")"); !ok {
		return nil, false
	}
	p.depth--
	span := p.since(keyword.Span.Start)
	switch keyword.Kind {
	case "optional":
		return &RailroadOptionalExpr{Span: span, Element: item}, true
	case "oneOrMore":
		return &RailroadOneOrMoreExpr{Span: span, Element: item}, true
	}
	return &RailroadZeroOrMoreExpr{Span: span, Element: item}, true
}

func (p *parser) railroadLeaf(keyword Token) (Expression, bool) {
	p.take()
	if _, ok := p.expect("("); !ok {
		return nil, false
	}
	text, ok := p.expect("STRING")
	if !ok {
		return nil, false
	}
	if _, ok := p.expect(")"); !ok {
		return nil, false
	}
	value := Value{Span: text.Span, Text: decodeEscapes(text.Text)}
	span := source.Span{Start: keyword.Span.Start, End: p.lastEnd()}
	switch keyword.Kind {
	case "terminal":
		return &RailroadTerminalExpr{Span: span, Value: value}, true
	case "nonterminal":
		return &RailroadNonTerminalExpr{Span: span, Name: value}, true
	}
	return &RailroadSpecialExpr{Span: span, Text: value}, true
}
