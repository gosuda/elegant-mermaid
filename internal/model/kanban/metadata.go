package kanban

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/kanban"
)

type reading struct {
	input   string
	at      []int
	span    source.Span
	wrapped bool
}

func newReading(data *syn.ShapeData) reading {
	var text strings.Builder
	var at []int
	for _, token := range data.Tokens {
		for i := range len(token.Text) {
			at = append(at, min(token.Span.Start+i, max(token.Span.End-1, token.Span.Start)))
		}
		text.WriteString(token.Text)
	}
	body := text.String()
	if strings.ContainsAny(body, "\r\n") {
		return reading{input: body, at: at, span: data.Span}
	}
	wrapped := make([]int, 0, len(at)+2)
	wrapped = append(wrapped, data.Span.Start)
	wrapped = append(wrapped, at...)
	wrapped = append(wrapped, max(data.Span.End-1, data.Span.Start))
	return reading{input: "{" + body + "}", at: wrapped, span: data.Span, wrapped: true}
}

func (m reading) blank() bool {
	if m.wrapped {
		return false
	}
	for line := range strings.Lines(m.input) {
		trimmed := strings.TrimLeft(line, " \t\r\n")
		if trimmed != "" && trimmed[0] != '#' {
			return false
		}
	}
	return true
}

func (r *resolver) applyMetadata(node *Node, data *syn.ShapeData) bool {
	m := newReading(data)
	doc, diags := syntax.ParseConfigYAML([]byte(m.input), 0, len(m.input))
	if len(diags) > 0 || m.blank() || doc.Kind == syntax.ValueNull {
		r.report(codeMalformedMetadata, "invalid node metadata", data.Span)
		return false
	}
	if doc.Kind != syntax.ValueMapping {
		return true
	}
	fields := make(map[string]syntax.ConfigEntry, len(doc.Entries))
	for _, entry := range doc.Entries {
		fields[entry.Key] = entry
	}
	if shape, ok := fields["shape"]; ok && truthy(shape.Value) && invalidShape(shape.Value) {
		r.invalidShape(m, shape)
		return false
	}
	return r.convert(node, fields, data.Span)
}

func (r *resolver) convert(node *Node, fields map[string]syntax.ConfigEntry, span source.Span) bool {
	targets := []struct {
		key  string
		into func(string)
	}{
		{"label", func(s string) { node.Label = syntax.DecodeEntities(s) }},
		{"icon", func(s string) { node.Icon = s }},
		{"assigned", func(s string) { node.Assigned = s }},
		{"ticket", func(s string) { node.Ticket = s }},
	}
	for _, target := range targets {
		entry, ok := fields[target.key]
		if !ok || !truthy(entry.Value) {
			continue
		}
		if !convertible(entry.Value) {
			r.report(codeMalformedMetadata, "invalid node metadata", span)
			return false
		}
		target.into(jsString(entry.Value))
	}
	if entry, ok := fields["priority"]; ok && truthy(entry.Value) {
		node.Priority, node.HasPriority = jsString(entry.Value), true
	}
	return true
}

func invalidShape(value syntax.ConfigValue) bool {
	return value.Kind != syntax.ValueString || strings.ToLower(value.Text) != value.Text || strings.Contains(value.Text, "_")
}

func (r *resolver) invalidShape(m reading, shape syntax.ConfigEntry) {
	start, end := valueSpan(m.input, shape.KeySpan.End)
	span := r.snap(m.sourceSpan(start, end))
	r.report(codeInvalidShape, "invalid shape "+jsString(shape.Value)+"; shape names must be lowercase without underscores", span)
}

func (m reading) sourceSpan(start, end int) source.Span {
	if len(m.at) == 0 {
		return m.span
	}
	from := m.at[min(start, len(m.at)-1)]
	to := from
	if end > start {
		to = m.at[min(end, len(m.at))-1] + 1
	}
	return source.Span{Start: from, End: max(from, min(to, m.span.End))}
}

func (r *resolver) snap(span source.Span) source.Span {
	for span.Start > 0 && span.Start < len(r.src) && !utf8.RuneStart(r.src[span.Start]) {
		span.Start--
	}
	for span.End < len(r.src) && !utf8.RuneStart(r.src[span.End]) {
		span.End++
	}
	return span
}

func valueSpan(input string, keyEnd int) (int, int) {
	colon := skipBlanks(input, keyEnd)
	if colon >= len(input) || input[colon] != ':' {
		return keyEnd, keyEnd
	}
	start := skipBlanks(input, colon+1)
	if start < len(input) && (input[start] == '"' || input[start] == '\'') {
		return start, quotedEnd(input, start)
	}
	return start, plainValueEnd(input, start)
}

func plainValueEnd(input string, start int) int {
	end := start
	for end < len(input) && !plainEnds(input, end) {
		end++
	}
	for end > start && (input[end-1] == ' ' || input[end-1] == '\t') {
		end--
	}
	return end
}

func skipBlanks(input string, at int) int {
	for at < len(input) && (input[at] == ' ' || input[at] == '\t') {
		at++
	}
	return at
}

func plainEnds(input string, at int) bool {
	switch input[at] {
	case ',', '\r', '\n', '}':
		return true
	case '#':
		return at > 0 && (input[at-1] == ' ' || input[at-1] == '\t')
	}
	return false
}

func quotedEnd(input string, start int) int {
	quote := input[start]
	for i := start + 1; i < len(input); i++ {
		switch {
		case quote == '"' && input[i] == '\\':
			i++
		case input[i] != quote:
		case quote == '\'' && i+1 < len(input) && input[i+1] == '\'':
			i++
		default:
			return i + 1
		}
	}
	return len(input)
}
