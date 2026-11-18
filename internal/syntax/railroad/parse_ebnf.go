package railroad

var ebnfStarts = []string{"(", "ID", "SPECIAL", "STRING", "[", "{"}

func ebnfPrimaryStart(kind string) bool {
	switch kind {
	case "STRING", "SPECIAL", "ID", "(", "[", "{":
		return true
	}
	return false
}

func (p *parser) ebnfChoice() (*EbnfChoice, bool) {
	start := p.tok().Span.Start
	out := &EbnfChoice{}
	for {
		sequence, ok := p.ebnfSequence()
		if !ok {
			return nil, false
		}
		out.Alternatives = append(out.Alternatives, *sequence)
		if p.kind() != "|" {
			break
		}
		p.take()
	}
	out.Span = p.since(start)
	return out, true
}

func (p *parser) ebnfSequence() (*EbnfSequence, bool) {
	start := p.tok().Span.Start
	out := &EbnfSequence{}
	for {
		term, ok := p.ebnfTerm()
		if !ok {
			return nil, false
		}
		out.Elements = append(out.Elements, *term)
		if p.kind() == "," {
			p.take()
			continue
		}
		if !ebnfPrimaryStart(p.kind()) {
			break
		}
	}
	out.Span = p.since(start)
	return out, true
}

func (p *parser) ebnfTerm() (*EbnfTerm, bool) {
	start := p.tok().Span.Start
	base, ok := p.ebnfPrimary()
	if !ok {
		return nil, false
	}
	term := &EbnfTerm{Base: base}
	levels := 0
	for {
		postfix, ok, more := p.ebnfPostfix(&levels)
		if !ok {
			return nil, false
		}
		if !more {
			break
		}
		term.Postfixes = append(term.Postfixes, postfix)
	}
	p.depth -= levels
	term.Span = p.since(start)
	return term, true
}

func (p *parser) ebnfPostfix(levels *int) (postfix EbnfPostfix, ok, more bool) {
	t := p.tok()
	switch t.Kind {
	case "?", "*", "+", "-":
	default:
		return nil, true, false
	}
	if !p.enter(t) {
		return nil, false, false
	}
	*levels++
	p.take()
	switch t.Kind {
	case "?":
		return &EbnfOptionalPostfix{Span: t.Span}, true, true
	case "*":
		return &EbnfZeroOrMorePostfix{Span: t.Span}, true, true
	case "+":
		return &EbnfOneOrMorePostfix{Span: t.Span}, true, true
	}
	except, ok := p.ebnfPrimary()
	if !ok {
		return nil, false, false
	}
	return &EbnfExceptionPostfix{Span: p.since(t.Span.Start), Except: except}, true, true
}

func (p *parser) ebnfPrimary() (EbnfPrimary, bool) {
	t := p.tok()
	switch t.Kind {
	case "STRING":
		p.take()
		return &EbnfTerminal{Span: t.Span, Value: Value{Span: t.Span, Text: decodeEscapes(t.Text)}}, true
	case "SPECIAL":
		p.take()
		return &EbnfSpecial{Span: t.Span, Text: Value{Span: t.Span, Text: trimJS(t.Text[1 : len(t.Text)-1])}}, true
	case "ID":
		p.take()
		return &EbnfNonTerminal{Span: t.Span, Name: Value{Span: t.Span, Text: t.Text}}, true
	case "(", "[", "{":
		return p.ebnfGroup(t)
	}
	p.fail(ebnfStarts...)
	return nil, false
}

func (p *parser) ebnfGroup(open Token) (EbnfPrimary, bool) {
	if !p.enter(open) {
		return nil, false
	}
	p.take()
	element, ok := p.ebnfChoice()
	if !ok {
		return nil, false
	}
	if _, ok := p.expect(ebnfCloser(open.Kind)); !ok {
		return nil, false
	}
	p.depth--
	span := p.since(open.Span.Start)
	switch open.Kind {
	case "(":
		return &EbnfGroup{Span: span, Element: element}, true
	case "[":
		return &EbnfOptional{Span: span, Element: element}, true
	}
	return &EbnfRepetition{Span: span, Element: element}, true
}

func ebnfCloser(open string) string {
	switch open {
	case "(":
		return ")"
	case "[":
		return "]"
	}
	return "}"
}
