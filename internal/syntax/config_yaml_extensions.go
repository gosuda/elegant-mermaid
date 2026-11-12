package syntax

import "strings"

func (r *configReader) yamlSequenceAt(p int) bool {
	return p < r.end && r.src[p] == '-' && r.atNodeBreak(p+1)
}

func (r *configReader) parseYAMLBlockNode(col, owner int) (ConfigValue, bool) {
	if r.yamlSequenceAt(r.pos) {
		return r.parseYAMLBlockSequence(col)
	}
	if r.nodePrefixFails(r.pos) {
		return ConfigValue{}, false
	}
	if r.src[r.pos] == '[' || r.src[r.pos] == '{' {
		return r.parseInlineValue(owner)
	}
	end, _ := splitLine(r.src, r.pos, r.end)
	if keyColonAt(r.src, r.pos, end) >= 0 {
		return r.parseYAMLBlockMap(col)
	}
	return r.parseInlineValue(owner)
}

func (r *configReader) parseYAMLBlockSequence(col int) (ConfigValue, bool) {
	start := r.pos
	if !r.enter(start) {
		return ConfigValue{}, false
	}
	out := ConfigValue{Kind: ValueSequence}
	for {
		if !r.yamlSequenceAt(r.pos) {
			r.failMalformed(r.pos)
			return ConfigValue{}, false
		}
		value, ok := r.parseYAMLSequenceItem(col)
		if !ok {
			return ConfigValue{}, false
		}
		out.Items = append(out.Items, value)
		if !r.skipBlankAndComments() {
			return ConfigValue{}, false
		}
		if r.pos >= r.end || r.lineIndentAt(r.pos) < col {
			break
		}
		if r.lineIndentAt(r.pos) != col {
			r.failMalformed(r.pos)
			return ConfigValue{}, false
		}
	}
	r.leave()
	out.Span = r.span(start, r.pos)
	return out, true
}

func (r *configReader) yamlContinuation(owner int) (int, int, bool) {
	_, p := splitLine(r.src, r.pos, r.end)
	blank := 0
	for p < r.end {
		end, next := splitLine(r.src, p, r.end)
		indent, content, tab := r.scanIndent(p, end)
		if tab >= 0 {
			r.failTab(tab)
			return 0, 0, false
		}
		if content == end {
			blank++
			p = next
			continue
		}
		if indent <= owner {
			return 0, 0, false
		}
		return content, blank, true
	}
	return 0, 0, false
}

func (r *configReader) parseYAMLScalar(owner int) (ConfigValue, bool) {
	if r.pos >= r.end {
		r.failMalformed(r.end)
		return ConfigValue{}, false
	}
	if r.src[r.pos] == '\'' || r.src[r.pos] == '"' {
		value, ok := r.parseYAMLQuoted(owner)
		if !ok {
			return value, ok
		}
		return value, r.finishLineValue()
	}
	start := r.pos
	value, ok := r.parsePlainBlockScalar()
	if !ok {
		return ConfigValue{}, false
	}
	last := value.Span.End - r.origin
	text := string(r.src[start:last])
	for {
		p, blank, more := r.yamlPlainContinuation(owner)
		if !more {
			break
		}
		r.pos = p
		next := r.readPlainBlockScalar()
		last = next.Span.End - r.origin
		text += yamlPlainFoldSeparator(blank) + string(r.src[p:last])
	}
	if r.failed {
		return ConfigValue{}, false
	}
	value = resolvePlain(text, r.span(start, last))
	return value, r.finishLineValue()
}

func (r *configReader) parseYAMLQuoted(owner int) (ConfigValue, bool) {
	start := r.pos
	quote := r.src[r.pos]
	r.pos++
	var b strings.Builder
	for r.pos < r.end {
		c := r.src[r.pos]
		if c == quote {
			if r.consumeYAMLQuote(quote, &b) {
				continue
			}
			return ConfigValue{Kind: ValueString, Text: b.String(), Span: r.span(start, r.pos)}, true
		}
		if !r.readYAMLQuotedContent(owner, quote, c, &b) {
			return ConfigValue{}, false
		}
	}
	r.failMalformed(r.end)
	return ConfigValue{}, false
}

func (r *configReader) readYAMLQuotedContent(owner int, quote, c byte, b *strings.Builder) bool {
	if r.yamlEscapedLineBreak(quote, c) {
		r.pos++
		return r.foldYAMLQuotedLine(owner, b, "")
	}
	if isLineBreak(c) {
		text := strings.TrimRight(b.String(), " \t")
		b.Reset()
		b.WriteString(text)
		return r.foldYAMLQuotedLine(owner, b, " ")
	}
	return r.readYAMLQuotedByte(quote, c, b)
}

func (r *configReader) parseYAMLPlainFlow(owner int) (ConfigValue, bool) {
	start := r.pos
	text, ok := r.plainFlowText(start)
	if !ok {
		return ConfigValue{}, false
	}
	last := start + len(text)
	for r.pos < r.end && isLineBreak(r.src[r.pos]) {
		p, blank, more := r.yamlContinuation(owner)
		if !more {
			break
		}
		if flowStop(r.src[p]) || r.src[p] == '#' {
			break
		}
		r.pos = p
		next, valid := r.plainFlowText(p)
		if !valid {
			return ConfigValue{}, false
		}
		if blank > 0 {
			text += strings.Repeat("\n", blank)
		} else {
			text += " "
		}
		text += next
		last = p + len(next)
	}
	if r.failed {
		return ConfigValue{}, false
	}
	return resolvePlain(text, r.span(start, last)), true
}

func (r *configReader) parseYAMLSequenceItem(col int) (ConfigValue, bool) {
	r.pos++
	r.skipInlineSpace()
	if !r.inlineValueStart() {
		return r.parseEntryValue(col, r.pos)
	}
	return r.parseYAMLBlockNode(r.pos-lineStart(r.src, r.pos), col)
}

func (r *configReader) yamlPlainContinuation(owner int) (int, int, bool) {
	end, _ := splitLine(r.src, r.pos, r.end)
	if skipLineSpaces(r.src, r.pos, end) < end {
		return 0, 0, false
	}
	p, blank, more := r.yamlContinuation(owner)
	if !more {
		return 0, 0, false
	}
	lineEnd, _ := splitLine(r.src, p, r.end)
	if r.src[p] == '#' || r.yamlSequenceAt(p) || keyColonAt(r.src, p, lineEnd) >= 0 {
		return 0, 0, false
	}
	return p, blank, true
}

func (r *configReader) consumeYAMLQuote(quote byte, b *strings.Builder) bool {
	r.pos++
	if quote != '\'' || r.pos >= r.end || r.src[r.pos] != '\'' {
		return false
	}
	b.WriteByte('\'')
	r.pos++
	return true
}

func (r *configReader) yamlEscapedLineBreak(quote, c byte) bool {
	return quote == '"' && c == '\\' && r.pos+1 < r.end && isLineBreak(r.src[r.pos+1])
}

func (r *configReader) foldYAMLQuotedLine(owner int, b *strings.Builder, separator string) bool {
	p, blank, ok := r.yamlContinuation(owner)
	if !ok {
		if !r.failed {
			r.failMalformed(r.pos)
		}
		return false
	}
	if blank > 0 {
		separator = strings.Repeat("\n", blank)
	}
	b.WriteString(separator)
	r.pos = p
	return true
}

func (r *configReader) readYAMLQuotedByte(quote, c byte, b *strings.Builder) bool {
	if quote == '"' {
		return r.readQuotedByte(b, c)
	}
	if c < 0x20 {
		r.failMalformed(r.pos)
		return false
	}
	b.WriteByte(c)
	r.pos++
	return true
}

func yamlPlainFoldSeparator(blank int) string {
	if blank > 0 {
		return strings.Repeat("\n", blank)
	}
	return " "
}
