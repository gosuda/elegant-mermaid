package railroad

func abnfElementStart(kind string) bool {
	switch kind {
	case "REPEAT", "EXACT_REPEAT", "STRING", "NUMVAL", "ID", "(", "[":
		return true
	}
	return false
}

func (p *parser) abnfAlternation() (*AbnfAlternation, bool) {
	start := p.tok().Span.Start
	out := &AbnfAlternation{}
	for {
		concatenation, ok := p.abnfConcatenation()
		if !ok {
			return nil, false
		}
		out.Alternatives = append(out.Alternatives, *concatenation)
		if p.kind() != "/" {
			break
		}
		p.take()
	}
	out.Span = p.since(start)
	return out, true
}

func (p *parser) abnfConcatenation() (*AbnfConcatenation, bool) {
	start := p.tok().Span.Start
	out := &AbnfConcatenation{}
	for {
		element, ok := p.abnfElement()
		if !ok {
			return nil, false
		}
		out.Elements = append(out.Elements, *element)
		if !abnfElementStart(p.kind()) {
			break
		}
	}
	out.Span = p.since(start)
	return out, true
}

func (p *parser) abnfElement() (*AbnfElement, bool) {
	start := p.tok().Span.Start
	element := &AbnfElement{}
	if kind := p.kind(); kind == "REPEAT" || kind == "EXACT_REPEAT" {
		repeat := p.tok()
		if !p.enter(repeat) {
			return nil, false
		}
		p.take()
		element.Repeat = &repeat
		defer func() { p.depth-- }()
	}
	primary, ok := p.abnfPrimary()
	if !ok {
		return nil, false
	}
	element.Primary = primary
	element.Span = p.since(start)
	return element, true
}

func (p *parser) abnfPrimary() (AbnfPrimary, bool) {
	t := p.tok()
	switch t.Kind {
	case "STRING":
		p.take()
		return &AbnfStringLiteral{Span: t.Span, Value: Value{Span: t.Span, Text: stripQuotes(t.Text)}}, true
	case "NUMVAL":
		p.take()
		return &AbnfNumVal{Span: t.Span, Value: Value{Span: t.Span, Text: t.Text}}, true
	case "ID":
		p.take()
		return &AbnfRuleName{Span: t.Span, Name: Value{Span: t.Span, Text: t.Text}}, true
	case "(", "[":
		return p.abnfGroup(t)
	}
	p.fail("(", "STRING", "NUMVAL", "ID", "[")
	return nil, false
}

func (p *parser) abnfGroup(open Token) (AbnfPrimary, bool) {
	if !p.enter(open) {
		return nil, false
	}
	p.take()
	element, ok := p.abnfAlternation()
	if !ok {
		return nil, false
	}
	closer := ")"
	if open.Kind == "[" {
		closer = "]"
	}
	if _, ok := p.expect(closer); !ok {
		return nil, false
	}
	p.depth--
	span := p.since(open.Span.Start)
	if open.Kind == "(" {
		return &AbnfGroup{Span: span, Element: element}, true
	}
	return &AbnfOptionalGroup{Span: span, Element: element}, true
}
