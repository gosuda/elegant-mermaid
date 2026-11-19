package icon

import (
	"fmt"
	"strings"
	"unicode/utf8"
)

const maxJSONDepth = 64

type jsonKind uint8

const (
	jsonNull jsonKind = iota
	jsonBool
	jsonNumber
	jsonString
	jsonArray
	jsonObject
)

type jsonMember struct {
	key   string
	value *jsonValue
}

type jsonValue struct {
	kind    jsonKind
	text    string
	members []jsonMember
}

func (v *jsonValue) member(key string) *jsonValue {
	if v.kind != jsonObject {
		return nil
	}
	for i := len(v.members) - 1; i >= 0; i-- {
		if v.members[i].key == key {
			return v.members[i].value
		}
	}
	return nil
}

type jsonError struct {
	at     int
	reason string
}

func (e *jsonError) Error() string {
	return fmt.Sprintf("invalid JSON at byte %d: %s", e.at, e.reason)
}

type jsonReader struct {
	text string
	at   int
}

func parseJSON(text string) (*jsonValue, error) {
	r := jsonReader{text: text}
	r.skipSpace()
	value, err := r.value(0)
	if err != nil {
		return nil, err
	}
	r.skipSpace()
	if r.at != len(r.text) {
		return nil, r.fail("trailing content")
	}
	return value, nil
}

func (r *jsonReader) fail(reason string) error {
	return &jsonError{at: r.at, reason: reason}
}

func (r *jsonReader) peek() (byte, bool) {
	if r.at >= len(r.text) {
		return 0, false
	}
	return r.text[r.at], true
}

func (r *jsonReader) skipSpace() {
	for r.at < len(r.text) && strings.IndexByte(" \t\r\n", r.text[r.at]) >= 0 {
		r.at++
	}
}

func (r *jsonReader) eat(b byte) bool {
	if c, ok := r.peek(); ok && c == b {
		r.at++
		return true
	}
	return false
}

func (r *jsonReader) enter(depth int) error {
	if depth >= maxJSONDepth {
		return r.fail("nesting is too deep")
	}
	return nil
}

func (r *jsonReader) value(depth int) (*jsonValue, error) {
	c, _ := r.peek()
	switch {
	case c == '{':
		return r.object(depth)
	case c == '[':
		return r.array(depth)
	case c == '"':
		text, err := r.string()
		return &jsonValue{kind: jsonString, text: text}, err
	case c == 't':
		return r.literal("true", jsonBool)
	case c == 'f':
		return r.literal("false", jsonBool)
	case c == 'n':
		return r.literal("null", jsonNull)
	case c == '-' || isDigit(c):
		return r.number()
	}
	return nil, r.fail("expected a value")
}

func (r *jsonReader) literal(word string, kind jsonKind) (*jsonValue, error) {
	if !strings.HasPrefix(r.text[r.at:], word) {
		return nil, r.fail("unknown literal")
	}
	r.at += len(word)
	return &jsonValue{kind: kind, text: word}, nil
}

func (r *jsonReader) object(depth int) (*jsonValue, error) {
	if err := r.enter(depth); err != nil {
		return nil, err
	}
	r.at++
	object := &jsonValue{kind: jsonObject}
	r.skipSpace()
	if r.eat('}') {
		return object, nil
	}
	for {
		member, err := r.member(depth)
		if err != nil {
			return nil, err
		}
		object.members = append(object.members, member)
		r.skipSpace()
		if r.eat(',') {
			continue
		}
		if r.eat('}') {
			return object, nil
		}
		return nil, r.fail("expected ',' or '}'")
	}
}

func (r *jsonReader) member(depth int) (jsonMember, error) {
	r.skipSpace()
	if c, _ := r.peek(); c != '"' {
		return jsonMember{}, r.fail("expected a member name")
	}
	key, err := r.string()
	if err != nil {
		return jsonMember{}, err
	}
	r.skipSpace()
	if !r.eat(':') {
		return jsonMember{}, r.fail("expected ':'")
	}
	r.skipSpace()
	value, err := r.value(depth + 1)
	return jsonMember{key: key, value: value}, err
}

func (r *jsonReader) array(depth int) (*jsonValue, error) {
	if err := r.enter(depth); err != nil {
		return nil, err
	}
	r.at++
	array := &jsonValue{kind: jsonArray}
	r.skipSpace()
	if r.eat(']') {
		return array, nil
	}
	for {
		r.skipSpace()
		value, err := r.value(depth + 1)
		if err != nil {
			return nil, err
		}
		array.members = append(array.members, jsonMember{value: value})
		r.skipSpace()
		if r.eat(',') {
			continue
		}
		if r.eat(']') {
			return array, nil
		}
		return nil, r.fail("expected ',' or ']'")
	}
}

func (r *jsonReader) number() (*jsonValue, error) {
	start := r.at
	for _, part := range []func() error{r.integerPart, r.fractionPart, r.exponentPart} {
		if err := part(); err != nil {
			return nil, err
		}
	}
	return &jsonValue{kind: jsonNumber, text: r.text[start:r.at]}, nil
}

func (r *jsonReader) integerPart() error {
	r.eat('-')
	switch c, _ := r.peek(); {
	case c == '0':
		r.at++
	case c >= '1' && c <= '9':
		r.digits()
	default:
		return r.fail("expected a digit")
	}
	return nil
}

func (r *jsonReader) fractionPart() error {
	if !r.eat('.') {
		return nil
	}
	if c, _ := r.peek(); !isDigit(c) {
		return r.fail("expected a fraction digit")
	}
	r.digits()
	return nil
}

func (r *jsonReader) exponentPart() error {
	if c, _ := r.peek(); c != 'e' && c != 'E' {
		return nil
	}
	r.at++
	if c, _ := r.peek(); c == '+' || c == '-' {
		r.at++
	}
	if c, _ := r.peek(); !isDigit(c) {
		return r.fail("expected an exponent digit")
	}
	r.digits()
	return nil
}

func (r *jsonReader) digits() {
	for r.at < len(r.text) && isDigit(r.text[r.at]) {
		r.at++
	}
}

func (r *jsonReader) string() (string, error) {
	r.at++
	var out strings.Builder
	for {
		c, ok := r.peek()
		if !ok {
			return "", r.fail("unterminated string")
		}
		r.at++
		switch {
		case c == '"':
			return out.String(), nil
		case c == '\\':
			if err := r.escape(&out); err != nil {
				return "", err
			}
		case c < 0x20:
			return "", r.fail("control character in string")
		default:
			out.WriteByte(c)
		}
	}
}

var simpleEscapes = map[byte]byte{'"': '"', '\\': '\\', '/': '/', 'b': '\b', 'f': '\f', 'n': '\n', 'r': '\r', 't': '\t'}

func (r *jsonReader) escape(out *strings.Builder) error {
	c, ok := r.peek()
	if !ok {
		return r.fail("unterminated escape")
	}
	r.at++
	if simple, found := simpleEscapes[c]; found {
		out.WriteByte(simple)
		return nil
	}
	if c != 'u' {
		return r.fail("invalid escape")
	}
	code, err := r.codePoint()
	if err != nil {
		return err
	}
	if !utf8.ValidRune(rune(code)) {
		return r.fail("invalid code point")
	}
	out.WriteRune(rune(code))
	return nil
}

func (r *jsonReader) codePoint() (uint32, error) {
	first, err := r.hex4()
	if err != nil || first < 0xd800 || first >= 0xdc00 {
		return first, err
	}
	if !r.eat('\\') || !r.eat('u') {
		return 0, r.fail("unpaired surrogate")
	}
	second, err := r.hex4()
	if err != nil {
		return 0, err
	}
	if second < 0xdc00 || second >= 0xe000 {
		return 0, r.fail("unpaired surrogate")
	}
	return 0x10000 + (first-0xd800)<<10 + (second - 0xdc00), nil
}

func (r *jsonReader) hex4() (uint32, error) {
	var value uint32
	for range 4 {
		c, _ := r.peek()
		digit, ok := hexDigit(c)
		if !ok {
			return 0, r.fail("expected a hex digit")
		}
		r.at++
		value = value*16 + digit
	}
	return value, nil
}

func hexDigit(c byte) (uint32, bool) {
	switch {
	case isDigit(c):
		return uint32(c - '0'), true
	case c >= 'a' && c <= 'f':
		return uint32(c-'a') + 10, true
	case c >= 'A' && c <= 'F':
		return uint32(c-'A') + 10, true
	}
	return 0, false
}
