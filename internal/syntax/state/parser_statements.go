package state

import "github.com/gosuda/elegant-mermaid/internal/source"

func (p *parser) statement(depth int) *Statement {
	if p.at >= len(p.tokens) {
		return nil
	}
	start := p.tokens[p.at].Span.Start
	node := p.statementNode(depth, start)
	if node == nil {
		return nil
	}
	return &Statement{Span: source.Span{Start: start, End: p.end()}, Node: node}
}

func (p *parser) statementNode(depth, start int) StatementNode {
	switch p.kind() {
	case kindID, "EDGE_STATE":
		return p.named()
	case "COMPOSIT_STATE", "STATE_DESCR":
		return p.composite(depth)
	case "FORK", "JOIN", "CHOICE", "CONCURRENT", "HIDE_EMPTY", "scale":
		return p.symbol()
	case "note":
		return p.note()
	case "classDef", "style", "class":
		return p.styles(start)
	case "CLICK":
		return p.click()
	}
	return p.directive()
}

func (p *parser) symbol() StatementNode {
	id, _ := p.take()
	switch id.Kind {
	case "CONCURRENT":
		return &Concurrent{}
	case "HIDE_EMPTY":
		return &HideEmpty{}
	case "scale":
		width, ok := p.expect("WIDTH")
		if !ok {
			return nil
		}
		return &Scale{Value: width}
	}
	kind := StereotypeChoice
	switch id.Kind {
	case "FORK":
		kind = StereotypeFork
	case "JOIN":
		kind = StereotypeJoin
	}
	return &Stereotype{ID: id, Kind: kind}
}

func directionValue(kind string) string {
	switch kind {
	case "direction_tb":
		return "TB"
	case "direction_bt":
		return "BT"
	case "direction_rl":
		return "RL"
	}
	return "LR"
}

func (p *parser) directive() StatementNode {
	switch p.kind() {
	case "acc_title":
		p.at++
		return p.accessibilityValue(&Accessibility{Title: true}, "acc_title_value")
	case "acc_descr":
		p.at++
		return p.accessibilityValue(&Accessibility{}, "acc_descr_value")
	case "acc_descr_multiline_value":
		t, _ := p.take()
		return &Accessibility{Value: t}
	case "direction_tb", "direction_bt", "direction_rl", "direction_lr":
		t, _ := p.take()
		return &Direction{Span: t.Span, Value: directionValue(t.Kind)}
	case "MULTIWORD":
		t, _ := p.take()
		p.issue(codeMultiword, "state name must be a single word: "+t.Text, t.Span)
		return nil
	case kindUnterminated:
		p.unterminated()
		return nil
	}
	p.unknownStatement()
	return nil
}

func (p *parser) accessibilityValue(node *Accessibility, kind string) StatementNode {
	value, ok := p.expect(kind)
	if !ok {
		return nil
	}
	node.Value = value
	return node
}

func (p *parser) unknownStatement() {
	t, ok := p.take()
	if !ok {
		return
	}
	p.recover()
	p.issue("state/unknown-statement", "unknown statement "+p.raw(t.Span), source.Span{Start: t.Span.Start, End: p.end()})
}

func (p *parser) optionalDescription() *Token {
	if p.kind() != "DESCR" {
		return nil
	}
	t, _ := p.take()
	return &t
}

func (p *parser) named() StatementNode {
	from, ok := p.id()
	if !ok {
		return nil
	}
	if p.kind() != "-->" {
		return &IDDeclaration{ID: from, Description: p.optionalDescription()}
	}
	arrow, _ := p.take()
	to, ok := p.id()
	if !ok {
		return nil
	}
	return &Transition{From: from, Arrow: arrow, To: to, Description: p.optionalDescription()}
}

func (p *parser) id() (IDStatement, bool) {
	if k := p.kind(); k != kindID && k != "EDGE_STATE" {
		p.unexpected("EDGE_STATE, ID")
		return IDStatement{}, false
	}
	id, _ := p.take()
	var class *Token
	if p.kind() == "STYLE_SEPARATOR" {
		p.at++
		t, ok := p.expect(kindID)
		if !ok {
			return IDStatement{}, false
		}
		class = &t
	}
	return IDStatement{Span: source.Span{Start: id.Span.Start, End: p.end()}, ID: id, CSSClass: class}, true
}

func (p *parser) composite(depth int) StatementNode {
	first, _ := p.take()
	c := &Composite{ID: first}
	if first.Kind == "STATE_DESCR" {
		if _, ok := p.expect("AS"); !ok {
			return nil
		}
		id, ok := p.expect(kindID)
		if !ok {
			return nil
		}
		c.ID, c.Description = id, &first
	}
	if p.kind() == kindNL && p.at+1 < len(p.tokens) && p.tokens[p.at+1].Kind == kindStructOpen {
		p.at++
	}
	if p.kind() != kindStructOpen {
		return c
	}
	b := p.body(depth)
	if b == nil {
		return nil
	}
	c.Body, c.Delimiters = &b.document, &b.delimiters
	return c
}

func (p *parser) note() StatementNode {
	p.at++
	if p.kind() == "NOTE_TEXT" {
		return p.floatingNote()
	}
	if k := p.kind(); k != "left_of" && k != "right_of" {
		p.unexpected("NOTE_TEXT, left_of, right_of")
		return nil
	}
	t, _ := p.take()
	target, ok := p.expect(kindID)
	if !ok {
		return nil
	}
	text, ok := p.expect("NOTE_TEXT")
	if !ok {
		return nil
	}
	return &Note{Position: NotePosition{Span: t.Span, Value: t.Kind}, Target: target, Text: text}
}

func (p *parser) floatingNote() StatementNode {
	text, _ := p.take()
	if _, ok := p.expect("AS"); !ok {
		return nil
	}
	id, ok := p.expect(kindID)
	if !ok {
		return nil
	}
	return &FloatingNote{Text: text, ID: id}
}

func (p *parser) pair(first, second string) (Token, Token, bool) {
	a, ok := p.expect(first)
	if !ok {
		return Token{}, Token{}, false
	}
	b, ok := p.expect(second)
	return a, b, ok
}

func (p *parser) styles(start int) StatementNode {
	head, _ := p.take()
	switch head.Kind {
	case "classDef":
		return p.classDef(start)
	case "style":
		targets, styles, ok := p.pair("STYLE_IDS", "STYLEDEF_STYLEOPTS")
		if !ok {
			return nil
		}
		return &StyleStatement{Span: source.Span{Start: start, End: p.end()}, Targets: targets, Styles: styles}
	}
	targets, class, ok := p.pair("CLASSENTITY_IDS", "STYLECLASS")
	if !ok {
		return nil
	}
	return &CSSClassStatement{Span: source.Span{Start: start, End: p.end()}, Targets: targets, Class: class}
}

func (p *parser) classDef(start int) StatementNode {
	if k := p.kind(); k != "CLASSDEF_ID" && k != "DEFAULT" {
		p.unexpected("CLASSDEF_ID, DEFAULT")
		return nil
	}
	id, _ := p.take()
	styles, ok := p.expect("CLASSDEF_STYLEOPTS")
	if !ok {
		return nil
	}
	return &ClassDefStatement{Span: source.Span{Start: start, End: p.end()}, ID: id, Styles: styles}
}

func (p *parser) click() StatementNode {
	p.at++
	target, ok := p.id()
	if !ok {
		return nil
	}
	href := p.kind() == "HREF"
	if href {
		p.at++
	}
	url, ok := p.expect("STRING")
	if !ok {
		return nil
	}
	c := &Click{Target: target, URL: url}
	if !href {
		tooltip, ok := p.expect("STRING")
		if !ok {
			return nil
		}
		c.Tooltip = &tooltip
	}
	if k := p.kind(); k != kindEOF && k != kindNL {
		p.unexpected("NL")
		return nil
	}
	return c
}
