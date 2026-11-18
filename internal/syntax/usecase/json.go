package usecase

import (
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

const maxJSONDepth = 64

type jsonFailure struct {
	span   source.Span
	reason string
	limit  bool
}

func (p *parser) jsonStatement() *JsonStatement {
	header, ok := p.expect("JSON_DECLARATION_START")
	if !ok {
		return nil
	}
	token, ok := p.expect("JSON_OBJECT_LITERAL")
	if !ok {
		return nil
	}
	object, ok := p.checkedJSON(token)
	if !ok {
		return nil
	}
	classes, ok := p.optionalClasses()
	if !ok {
		return nil
	}
	return &JsonStatement{Span: p.span(header.Span.Start), Header: header, ID: p.jsonIdentifier(header), Object: object, Classes: classes}
}

func (p *parser) checkedJSON(token Token) (JsonObject, bool) {
	reader := jsonReader{text: token.Text, cleaned: p.cleaned, base: p.cleaned.Index(token.Span.Start)}
	object, failure := reader.object(1)
	if failure == nil {
		return object, true
	}
	code, message := "usecase/invalid-json", "invalid JSON object: "+failure.reason
	if failure.limit {
		code, message = "limit/nesting-depth", "nesting depth exceeds 64"
	}
	p.issue(code, message, failure.span)
	return JsonObject{}, false
}

func (p *parser) jsonIdentifier(header Token) Token {
	tail := strings.TrimLeft(header.Text[len("json"):], " \t")
	start := p.cleaned.Index(header.Span.Start) + len(header.Text) - len(tail)
	text := tail[:wordLen(tail)]
	return Token{Kind: "IDENTIFIER", Text: text, Span: p.cleaned.Span(start, start+len(text))}
}

type jsonReader struct {
	text    string
	cleaned *source.Cleaned
	base    int
	at      int
}

func (r *jsonReader) byteAt() (byte, bool) {
	if r.at < len(r.text) {
		return r.text[r.at], true
	}
	return 0, false
}

func (r *jsonReader) is(b byte) bool {
	c, ok := r.byteAt()
	return ok && c == b
}

func (r *jsonReader) ws() {
	for r.at < len(r.text) && strings.IndexByte(" \t\r\n", r.text[r.at]) >= 0 {
		r.at++
	}
}

func (r *jsonReader) fail(reason string) *jsonFailure {
	size := 0
	if r.at < len(r.text) {
		_, size = utf8.DecodeRuneInString(r.text[r.at:])
	}
	return &jsonFailure{span: r.cleaned.Span(r.base+r.at, r.base+r.at+size), reason: reason}
}

func (r *jsonReader) span(start int) source.Span {
	return r.cleaned.Span(r.base+start, r.base+r.at)
}

func (r *jsonReader) require(b byte) *jsonFailure {
	r.ws()
	if !r.is(b) {
		return r.fail("unexpected token")
	}
	r.at++
	return nil
}

func (r *jsonReader) depth(depth int) *jsonFailure {
	if depth <= maxJSONDepth {
		return nil
	}
	failure := r.fail("nesting depth exceeds 64")
	failure.limit = true
	return failure
}

func (r *jsonReader) object(depth int) (JsonObject, *jsonFailure) {
	r.ws()
	if failure := r.depth(depth); failure != nil {
		return JsonObject{}, failure
	}
	start := r.at
	if failure := r.require('{'); failure != nil {
		return JsonObject{}, failure
	}
	r.ws()
	properties, failure := r.properties(depth)
	if failure != nil {
		return JsonObject{}, failure
	}
	if failure := r.require('}'); failure != nil {
		return JsonObject{}, failure
	}
	return JsonObject{Span: r.span(start), Properties: properties}, nil
}

func (r *jsonReader) properties(depth int) ([]JsonProperty, *jsonFailure) {
	var properties []JsonProperty
	if r.is('}') {
		return properties, nil
	}
	for {
		key, failure := r.str()
		if failure != nil {
			return nil, failure
		}
		if failure = r.require(':'); failure != nil {
			return nil, failure
		}
		value, failure := r.value(depth)
		if failure != nil {
			return nil, failure
		}
		properties = append(properties, JsonProperty{Span: source.Span{Start: key.Span.Start, End: value.Span.End}, Key: key, Value: value})
		r.ws()
		if !r.is(',') {
			return properties, nil
		}
		r.at++
	}
}

func (r *jsonReader) array(depth int) ([]JsonValue, *jsonFailure) {
	if failure := r.depth(depth); failure != nil {
		return nil, failure
	}
	if failure := r.require('['); failure != nil {
		return nil, failure
	}
	r.ws()
	var values []JsonValue
	if !r.is(']') {
		for {
			value, failure := r.value(depth)
			if failure != nil {
				return nil, failure
			}
			values = append(values, value)
			r.ws()
			if !r.is(',') {
				break
			}
			r.at++
		}
	}
	if failure := r.require(']'); failure != nil {
		return nil, failure
	}
	return values, nil
}

func (r *jsonReader) value(depth int) (JsonValue, *jsonFailure) {
	r.ws()
	start := r.at
	var value JsonValue
	var failure *jsonFailure
	switch c, _ := r.byteAt(); c {
	case '{':
		value.Kind = JSONObject
		value.Object, failure = r.object(depth + 1)
	case '[':
		value.Kind = JSONArray
		value.Array, failure = r.array(depth + 1)
	case '"':
		value.Kind = JSONScalar
		value.Scalar, failure = r.str()
	default:
		value.Kind = JSONScalar
		value.Scalar, failure = r.scalar()
	}
	if failure != nil {
		return JsonValue{}, failure
	}
	value.Span = r.span(start)
	return value, nil
}

func (r *jsonReader) str() (Token, *jsonFailure) {
	r.ws()
	start := r.at
	if failure := r.require('"'); failure != nil {
		return Token{}, failure
	}
	for {
		c, ok := r.byteAt()
		switch {
		case ok && c == '"':
			r.at++
			return r.token("JSON_STRING", start), nil
		case ok && c == '\\':
			r.at++
			if failure := r.escape(); failure != nil {
				return Token{}, failure
			}
		case !ok || c < 0x20:
			return Token{}, r.fail("invalid string")
		default:
			r.at++
		}
	}
}

func (r *jsonReader) escape() *jsonFailure {
	c, _ := r.byteAt()
	switch c {
	case '"', '\\', '/', 'b', 'f', 'n', 'r', 't':
		r.at++
	case 'u':
		r.at++
		for range 4 {
			if d, ok := r.byteAt(); !ok || !isHexDigit(d) {
				return r.fail("invalid unicode escape")
			}
			r.at++
		}
	default:
		return r.fail("invalid escape")
	}
	return nil
}

func (r *jsonReader) scalar() (Token, *jsonFailure) {
	start := r.at
	for _, literal := range [...]struct{ text, kind string }{{"true", "JSON_TRUE"}, {"false", "JSON_FALSE"}, {"null", "JSON_NULL"}} {
		if strings.HasPrefix(r.text[r.at:], literal.text) {
			r.at += len(literal.text)
			return r.token(literal.kind, start), nil
		}
	}
	if failure := r.number(); failure != nil {
		return Token{}, failure
	}
	return r.token("JSON_NUMBER", start), nil
}

func (r *jsonReader) token(kind string, start int) Token {
	return Token{Kind: kind, Text: r.text[start:r.at], Span: r.span(start)}
}

func (r *jsonReader) number() *jsonFailure {
	if r.is('-') {
		r.at++
	}
	switch c, _ := r.byteAt(); {
	case c == '0':
		r.at++
	case '1' <= c && c <= '9':
		r.digits()
	default:
		return r.fail("expected value")
	}
	if failure := r.fraction(); failure != nil {
		return failure
	}
	return r.exponent()
}

func (r *jsonReader) fraction() *jsonFailure {
	if !r.is('.') {
		return nil
	}
	r.at++
	return r.requireDigits()
}

func (r *jsonReader) exponent() *jsonFailure {
	if !r.is('e') && !r.is('E') {
		return nil
	}
	r.at++
	if r.is('+') || r.is('-') {
		r.at++
	}
	return r.requireDigits()
}

func (r *jsonReader) digits() {
	r.at += countWhile(r.text[r.at:], isDigit)
}

func (r *jsonReader) requireDigits() *jsonFailure {
	if c, ok := r.byteAt(); !ok || !isDigit(c) {
		return r.fail("expected digit")
	}
	r.digits()
	return nil
}
