package class

import "strings"

func marker(kind string) bool {
	return kind == "o" || kind == "*" || kind == "<" || kind == ">" || kind == "<|" || kind == "|>" || kind == "()"
}

func (p *parser) named() (Statement, bool) {
	from, ok := p.name()
	s := Statement{Kind: "member", Span: from.Span}
	if !ok {
		return s, false
	}
	if p.accept(":") {
		text, ok := p.memberText()
		s.Member = &MemberStatement{Name: from, Text: text, Span: from.Span}
		return s, ok
	}
	if p.statementEnds() {
		return s, true
	}
	r := &RelationStatement{From: from, Span: from.Span}
	if p.peek().Kind == "STR" {
		r.FromMultiplicity = p.take().Text
	}
	relation, ok := p.relation()
	r.Relation = relation
	if !ok {
		return s, false
	}
	if p.peek().Kind == "STR" {
		r.ToMultiplicity = p.take().Text
	}
	to, ok := p.name()
	r.To = to
	if !ok {
		return s, false
	}
	if p.accept(":") {
		label, ok := p.memberText()
		r.Label = label
		if !ok {
			return s, false
		}
	}
	s.Kind, s.Relation = "relation", r
	return s, true
}

func (p *parser) statementEnds() bool {
	switch p.peek().Kind {
	case "NEWLINE", "EOF", "}":
		return true
	}
	return false
}

func (p *parser) relation() (Relation, bool) {
	r := Relation{Span: p.peek().Span}
	if marker(p.peek().Kind) {
		r.Start = RelationType(p.take().Text)
	}
	switch p.peek().Kind {
	case "--", "..":
		r.Line = LineType(p.take().Kind)
	default:
		p.unexpected(p.peek(), "DOTTED_LINE, LINE")
		return r, false
	}
	if marker(p.peek().Kind) {
		r.End = RelationType(p.take().Text)
	}
	r.Span.End = p.tokens[p.at-1].Span.End
	return r, true
}

func (p *parser) note() (*NoteStatement, bool) {
	start := p.take().Span.Start
	n := &NoteStatement{}
	if p.accept("for") {
		name, ok := p.name()
		n.Name = name
		if !ok {
			return n, false
		}
	}
	t, ok := p.expect("STR", "STR")
	if !ok {
		return n, false
	}
	n.Text = t.Text
	n.Span.Start, n.Span.End = start, t.Span.End
	return n, true
}

func (p *parser) annotation() (*AnnotationStatement, bool) {
	start := p.take().Span.Start
	a := &AnnotationStatement{Annotation: p.take().Text}
	if _, ok := p.expect(">>", "ANNOTATION_END"); !ok {
		return a, false
	}
	name, ok := p.name()
	a.Name = name
	if !ok {
		return a, false
	}
	a.Span.Start, a.Span.End = start, a.Name.Span.End
	return a, true
}

func (p *parser) style() (*StyleStatement, bool) {
	t := p.take()
	s := &StyleStatement{Span: t.Span}
	if t.Kind == "cssClass" {
		targets, ok := p.expect("STR", "STR")
		if !ok {
			return s, false
		}
		s.Targets = strings.Split(targets.Text, ",")
		s.Text = p.take().Text
	} else {
		s.Targets = append(s.Targets, p.take().Text)
		for p.accept(",") {
			s.Targets = append(s.Targets, p.take().Text)
		}
		s.Text = p.lineText()
	}
	s.Span.End = p.tokens[p.at-1].Span.End
	return s, true
}

func (p *parser) click() (*ClickStatement, bool) {
	t := p.take()
	name, ok := p.name()
	c := &ClickStatement{Action: t.Kind, Name: name, Target: "_blank", Span: t.Span}
	if !ok {
		return c, false
	}
	if p.accept("href") {
		c.Action = "link"
	}
	if !p.clickValue(c) {
		return c, false
	}
	if p.peek().Kind == "STR" {
		c.Tooltip = p.take().Text
	}
	if p.peek().Kind == "ALPHA" {
		c.Target = p.take().Text
	}
	c.Span.End = p.tokens[p.at-1].Span.End
	return c, true
}

func (p *parser) clickValue(c *ClickStatement) bool {
	if p.accept("call") {
		c.Action = "callback"
		return p.callback(c)
	}
	value, ok := p.expect("STR", "STR")
	if ok {
		c.Value = value.Text
	}
	return ok
}

func (p *parser) callback(c *ClickStatement) bool {
	c.Value = p.take().Text
	if p.accept("()") {
		return true
	}
	if _, ok := p.expect("(", "("); !ok {
		return false
	}
	start := p.peek().Span.Start
	for !p.end() && p.peek().Kind != ")" && p.peek().Kind != "NEWLINE" {
		p.take()
	}
	end := p.peek().Span.Start
	c.Arguments = p.text(start, end)
	_, ok := p.expect(")", ")")
	return ok
}

func (p *parser) memberText() (string, bool) {
	start, end := p.peek().Span.Start, p.peek().Span.Start
	for !p.statementEnds() {
		t := p.take()
		end = t.Span.End
		if t.Kind == ":" || t.Kind == ";" || t.Kind == ":::" {
			p.unexpected(t, "NEWLINE")
			p.recover()
			return "", false
		}
	}
	return strings.TrimSpace(p.text(start, end)), true
}
