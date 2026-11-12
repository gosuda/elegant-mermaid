package class

import "strings"

func marker(kind string) bool {
	return kind == "o" || kind == "*" || kind == "<" || kind == ">" || kind == "<|" || kind == "|>" || kind == "()"
}

func (p *parser) named() Statement {
	from := p.name()
	s := Statement{Kind: "member", Span: from.Span}
	if p.accept(":") {
		s.Member = &MemberStatement{Name: from, Text: p.memberText(), Span: from.Span}
		return s
	}
	r := &RelationStatement{From: from, Span: from.Span}
	if p.peek().Kind == "STR" {
		r.FromMultiplicity = p.take().Text
	}
	r.Relation = p.relation()
	if r.Relation.Line == "" {
		return s
	}
	if p.peek().Kind == "STR" {
		r.ToMultiplicity = p.take().Text
	}
	r.To = p.name()
	if p.accept(":") {
		r.Label = p.memberText()
	}
	s.Kind, s.Relation = "relation", r
	return s
}

func (p *parser) relation() Relation {
	r := Relation{Span: p.peek().Span}
	if marker(p.peek().Kind) {
		r.Start = RelationType(p.take().Text)
	}
	switch p.peek().Kind {
	case "--", "..":
		r.Line = LineType(p.take().Kind)
	case "NEWLINE", "EOF", "}":
		return r
	default:
		p.unexpected(p.peek(), "DOTTED_LINE, LINE")
		return r
	}
	if marker(p.peek().Kind) {
		r.End = RelationType(p.take().Text)
	}
	r.Span.End = p.tokens[p.at-1].Span.End
	return r
}

func (p *parser) note() *NoteStatement {
	start := p.take().Span.Start
	n := &NoteStatement{}
	if p.accept("for") {
		n.Name = p.name()
	}
	t := p.take()
	if t.Kind != "STR" {
		p.unexpected(t, "STR")
	}
	n.Text = t.Text
	n.Span.Start, n.Span.End = start, t.Span.End
	return n
}

func (p *parser) annotation() *AnnotationStatement {
	start := p.take().Span.Start
	a := &AnnotationStatement{Annotation: p.take().Text}
	if !p.accept(">>") {
		p.unexpected(p.peek(), "ANNOTATION_END")
	}
	a.Name = p.name()
	a.Span.Start, a.Span.End = start, a.Name.Span.End
	return a
}

func (p *parser) style() *StyleStatement {
	t := p.take()
	s := &StyleStatement{Span: t.Span}
	if t.Kind == "cssClass" {
		targets := p.take()
		if targets.Kind != "STR" {
			p.unexpected(targets, "STR")
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
	return s
}

func (p *parser) click() *ClickStatement {
	t := p.take()
	c := &ClickStatement{Action: t.Kind, Name: p.name(), Target: "_blank", Span: t.Span}
	if p.accept("href") {
		c.Action = "link"
	}
	if p.accept("call") {
		c.Action = "callback"
		p.callback(c)
	} else {
		value := p.take()
		if value.Kind != "STR" {
			p.unexpected(value, "STR")
		}
		c.Value = value.Text
	}
	if p.peek().Kind == "STR" {
		c.Tooltip = p.take().Text
	}
	if p.peek().Kind == "ALPHA" {
		c.Target = p.take().Text
	}
	c.Span.End = p.tokens[p.at-1].Span.End
	return c
}

func (p *parser) callback(c *ClickStatement) {
	c.Value = p.take().Text
	if p.accept("()") {
		return
	}
	if !p.accept("(") {
		p.unexpected(p.peek(), "(")
		return
	}
	start := p.peek().Span.Start
	for !p.end() && p.peek().Kind != ")" && p.peek().Kind != "NEWLINE" {
		p.take()
	}
	end := p.peek().Span.Start
	c.Arguments = string(p.src[start:end])
	if !p.accept(")") {
		p.unexpected(p.peek(), ")")
	}
}

func (p *parser) memberText() string {
	start, end := p.peek().Span.Start, p.peek().Span.Start
	for !p.end() && p.peek().Kind != "NEWLINE" {
		t := p.take()
		end = t.Span.End
		if t.Kind == ":" || t.Kind == ";" {
			p.unexpected(t, "NEWLINE")
			p.recover()
			break
		}
	}
	return strings.TrimSpace(string(p.src[start:end]))
}
