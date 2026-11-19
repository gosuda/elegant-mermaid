package railroad

func pegPrefixStart(kind string) bool {
	switch kind {
	case "&", "!", "STRING", "ID", "(", ".":
		return true
	}
	return false
}

func (p *parser) pegChoice() (*PegOrderedChoice, bool) {
	start := p.tok().Span.Start
	out := &PegOrderedChoice{}
	for {
		sequence, ok := p.pegSequence()
		if !ok {
			return nil, false
		}
		out.Alternatives = append(out.Alternatives, *sequence)
		if p.kind() != "/" {
			break
		}
		p.take()
	}
	out.Span = p.since(start)
	return out, true
}

func (p *parser) pegSequence() (*PegSequence, bool) {
	start := p.tok().Span.Start
	out := &PegSequence{}
	for {
		prefix, ok := p.pegPrefix()
		if !ok {
			return nil, false
		}
		out.Elements = append(out.Elements, *prefix)
		if !pegPrefixStart(p.kind()) {
			break
		}
	}
	out.Span = p.since(start)
	return out, true
}

func (p *parser) pegPrefix() (*PegPrefix, bool) {
	start := p.tok().Span.Start
	prefix := &PegPrefix{}
	levels := 0
	if kind := p.kind(); kind == "&" || kind == "!" {
		operator := p.tok()
		if !p.enter(operator) {
			return nil, false
		}
		levels++
		p.take()
		prefix.Operator = &operator
	}
	suffix, ok := p.pegSuffix(&levels)
	if !ok {
		return nil, false
	}
	p.depth -= levels
	prefix.Suffix = *suffix
	prefix.Span = p.since(start)
	return prefix, true
}

func (p *parser) pegSuffix(levels *int) (*PegSuffix, bool) {
	start := p.tok().Span.Start
	primary, ok := p.pegPrimary()
	if !ok {
		return nil, false
	}
	suffix := &PegSuffix{Primary: primary}
	if kind := p.kind(); kind == "?" || kind == "*" || kind == "+" {
		operator := p.tok()
		if !p.enter(operator) {
			return nil, false
		}
		*levels++
		p.take()
		suffix.Operator = &operator
	}
	suffix.Span = p.since(start)
	return suffix, true
}

func (p *parser) pegPrimary() (PegPrimary, bool) {
	t := p.tok()
	switch t.Kind {
	case "STRING":
		p.take()
		return &PegLiteral{Span: t.Span, Value: Value{Span: t.Span, Text: decodeEscapes(t.Text)}}, true
	case "ID":
		p.take()
		return &PegIdentifier{Span: t.Span, Name: Value{Span: t.Span, Text: t.Text}}, true
	case ".":
		p.take()
		return &PegAny{Span: t.Span}, true
	case "(":
		return p.pegGroup(t)
	}
	p.fail("(", "ID", "STRING", ".")
	return nil, false
}

func (p *parser) pegGroup(open Token) (PegPrimary, bool) {
	if !p.enter(open) {
		return nil, false
	}
	p.take()
	element, ok := p.pegChoice()
	if !ok {
		return nil, false
	}
	if _, ok := p.expect(")"); !ok {
		return nil, false
	}
	p.depth--
	return &PegGroup{Span: p.since(open.Span.Start), Element: element}, true
}
