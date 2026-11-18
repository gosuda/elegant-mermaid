package syntax

import (
	"github.com/gosuda/elegant-mermaid/internal/diag"
)

func ParseConfigJSON(src []byte, start, end int) (ConfigValue, []diag.Diagnostic) {
	value, diags, _ := parseConfigJSON(src, start, end)
	return value, diags
}

func parseConfigJSON(src []byte, start, end int) (ConfigValue, []diag.Diagnostic, bool) {
	r := newJSONReader(src, start, end)
	value, ok := r.parseJSONDocument()
	if !ok {
		value = emptyNullAt(start + r.end)
	}
	return value, r.diags, ok
}

func newJSONReader(src []byte, start, end int) *configReader {
	if start < 0 {
		start = 0
	}
	if end > len(src) {
		end = len(src)
	}
	if start > end {
		start = end
	}
	body := make([]byte, end-start)
	for i := start; i < end; i++ {
		if src[i] == '\'' {
			body[i-start] = '"'
			continue
		}
		body[i-start] = src[i]
	}
	r := newConfigReader(body, 0, len(body), start)
	r.jsonMode = true
	return r
}

func (r *configReader) parseJSONDocument() (ConfigValue, bool) {
	r.skipJSONSpace()
	if r.pos >= r.end || r.src[r.pos] != '{' {
		r.failMalformed(r.pos)
		return ConfigValue{}, false
	}
	value, ok := r.parseJSONValue()
	if !ok {
		return ConfigValue{}, false
	}
	r.skipJSONSpace()
	if r.pos < r.end {
		r.failMalformed(r.pos)
		return ConfigValue{}, false
	}
	return value, true
}

func (r *configReader) skipJSONSpace() {
	for r.pos < r.end && isConfigSpace(r.src[r.pos]) {
		r.pos++
	}
}

func (r *configReader) parseJSONValue() (ConfigValue, bool) {
	if r.pos >= r.end {
		r.failMalformed(r.end)
		return ConfigValue{}, false
	}
	switch b := r.src[r.pos]; {
	case b == '{':
		return r.parseJSONObject()
	case b == '[':
		return r.parseJSONArray()
	case b == '"':
		return r.parseDoubleQuoted()
	case b == '-' || isDigit(b):
		return r.parseJSONNumber()
	}
	return r.parseJSONLiteral()
}

func (r *configReader) parseJSONObject() (ConfigValue, bool) {
	start := r.pos
	if !r.enter(start) {
		return ConfigValue{}, false
	}
	r.pos++
	out := ConfigValue{Kind: ValueMapping}
	r.skipJSONSpace()
	ok := r.jsonClose('}') || r.parseJSONMembers(&out)
	if !ok {
		return ConfigValue{}, false
	}
	r.leave()
	out.Span = r.span(start, r.pos)
	return out, true
}

func (r *configReader) parseJSONMembers(out *ConfigValue) bool {
	for {
		ok, done := r.parseJSONMember(out)
		if !ok || done {
			return ok
		}
	}
}

func (r *configReader) parseJSONMember(out *ConfigValue) (bool, bool) {
	if r.pos >= r.end || r.src[r.pos] != '"' {
		r.failMalformed(r.pos)
		return false, false
	}
	key, ok := r.parseDoubleQuoted()
	if !ok {
		return false, false
	}
	r.skipJSONSpace()
	if !r.jsonClose(':') {
		r.failMalformed(r.pos)
		return false, false
	}
	r.skipJSONSpace()
	value, ok := r.parseJSONValue()
	if !ok {
		return false, false
	}
	r.appendEntry(out, key.Text, key.Span, value)
	r.skipJSONSpace()
	if r.jsonClose('}') {
		return true, true
	}
	if !r.jsonClose(',') {
		r.failMalformed(r.pos)
		return false, false
	}
	r.skipJSONSpace()
	return true, false
}

func (r *configReader) jsonClose(b byte) bool {
	if r.pos < r.end && r.src[r.pos] == b {
		r.pos++
		return true
	}
	return false
}

func (r *configReader) parseJSONArray() (ConfigValue, bool) {
	start := r.pos
	if !r.enter(start) {
		return ConfigValue{}, false
	}
	r.pos++
	out := ConfigValue{Kind: ValueSequence}
	r.skipJSONSpace()
	ok := r.jsonClose(']') || r.parseJSONItems(&out)
	if !ok {
		return ConfigValue{}, false
	}
	r.leave()
	out.Span = r.span(start, r.pos)
	return out, true
}

func (r *configReader) parseJSONItems(out *ConfigValue) bool {
	for {
		item, ok := r.parseJSONValue()
		if !ok {
			return false
		}
		out.Items = append(out.Items, item)
		r.skipJSONSpace()
		if r.jsonClose(']') {
			return true
		}
		if !r.jsonClose(',') {
			r.failMalformed(r.pos)
			return false
		}
		r.skipJSONSpace()
	}
}

type jsonNumber struct {
	end     int
	integer bool
}

func (r *configReader) parseJSONNumber() (ConfigValue, bool) {
	start := r.pos
	number, ok := r.scanJSONNumber(start)
	if !ok {
		return ConfigValue{}, false
	}
	kind := ValueDecimal
	if number.integer {
		kind = ValueInteger
	}
	text := string(r.src[start:number.end])
	r.pos = number.end
	return ConfigValue{Kind: kind, Text: text, Span: r.span(start, number.end)}, true
}

func (r *configReader) scanJSONNumber(start int) (jsonNumber, bool) {
	end := start
	if r.src[end] == '-' {
		end++
	}
	digits, end := jsonDigitsEnd(r.src, end, r.end)
	if !digits {
		r.failMalformed(end)
		return jsonNumber{}, false
	}
	number := jsonNumber{end: end, integer: true}
	if !r.scanJSONFraction(&number) || !r.scanJSONExponent(&number) {
		return jsonNumber{}, false
	}
	return number, true
}

func (r *configReader) scanJSONFraction(number *jsonNumber) bool {
	if number.end >= r.end || r.src[number.end] != '.' {
		return true
	}
	digits, next := jsonDigitsEnd(r.src, number.end+1, r.end)
	if !digits {
		r.failMalformed(next)
		return false
	}
	number.end = next
	number.integer = false
	return true
}

func (r *configReader) scanJSONExponent(number *jsonNumber) bool {
	if number.end >= r.end || (r.src[number.end] != 'e' && r.src[number.end] != 'E') {
		return true
	}
	next, ok := jsonExponentEnd(r.src, number.end+1, r.end)
	if !ok {
		r.failMalformed(next)
		return false
	}
	number.end = next
	number.integer = false
	return true
}

func jsonDigitsEnd(src []byte, from, end int) (bool, int) {
	i := from
	for i < end && isDigit(src[i]) {
		i++
	}
	return i > from, i
}

func jsonExponentEnd(src []byte, from, end int) (int, bool) {
	i := from
	if i < end && (src[i] == '+' || src[i] == '-') {
		i++
	}
	found, next := jsonDigitsEnd(src, i, end)
	return next, found
}

func (r *configReader) parseJSONLiteral() (ConfigValue, bool) {
	for _, literal := range []string{"true", "false", "null"} {
		if r.src[r.pos] == literal[0] {
			return r.jsonLiteral(literal)
		}
	}
	r.failMalformed(r.pos)
	return ConfigValue{}, false
}

// jsonLiteral reads one lowercase literal and fails at the first byte that the
// literal does not accept (preprocessing-002).
func (r *configReader) jsonLiteral(literal string) (ConfigValue, bool) {
	start := r.pos
	for k := 0; k < len(literal); k++ {
		if start+k >= r.end || r.src[start+k] != literal[k] {
			r.failMalformed(start + k)
			return ConfigValue{}, false
		}
	}
	r.pos = start + len(literal)
	span := r.span(start, r.pos)
	switch literal {
	case "true":
		return ConfigValue{Kind: ValueBool, Bool: true, Span: span}, true
	case "false":
		return ConfigValue{Kind: ValueBool, Bool: false, Span: span}, true
	}
	return ConfigValue{Kind: ValueNull, Span: span}, true
}
