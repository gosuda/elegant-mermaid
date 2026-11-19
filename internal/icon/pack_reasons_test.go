package icon

import (
	"errors"
	"strings"
	"testing"
)

func nestedArrays(levels int) string {
	return `{"prefix":"p","x":` + strings.Repeat("[", levels) + strings.Repeat("]", levels) + `,"icons":{}}`
}

func TestParsePackReasons(t *testing.T) {
	for _, c := range []struct{ name, data, reason string }{
		{"empty", ``, "invalid JSON at byte 0: expected a value"},
		{"invalid UTF-8", "{\"prefix\":\"\xff\"}", "invalid UTF-8"},
		{"array root", `[]`, "the root must be an object"},
		{"no prefix", `{"icons":{}}`, "missing string prefix"},
		{"numeric prefix", `{"prefix":5,"icons":{}}`, "missing string prefix"},
		{"capitalised key", `{"Prefix":"p","icons":{}}`, "missing string prefix"},
		{"empty prefix", `{"prefix":"","icons":{}}`, "the prefix must not be empty"},
		{"last duplicate wins", `{"prefix":"p","prefix":"","icons":{}}`, "the prefix must not be empty"},
		{"no icons", `{"prefix":"p"}`, "missing icons object"},
		{"icons array", `{"prefix":"p","icons":[]}`, "missing icons object"},
		{"null icon", `{"prefix":"p","icons":{"a":null}}`, "icon a must be an object"},
		{"no body", `{"prefix":"p","icons":{"a":{}}}`, "icon a needs a string body"},
		{"first bad icon", `{"prefix":"p","icons":{"b":{"body":5},"a":{}}}`, "icon b needs a string body"},
		{"string width", `{"prefix":"p","icons":{"a":{"body":"","width":"16"}}}`, "width must be a number"},
		{"null default width", `{"prefix":"p","width":null,"icons":{}}`, "width must be a number"},
		{"exponent width", `{"prefix":"p","icons":{"a":{"body":"","width":1e1}}}`, "width is out of range"},
		{"seven digit height", `{"prefix":"p","icons":{"a":{"body":"","height":1000000}}}`, "height is out of range"},
		{"seven fraction digits", `{"prefix":"p","left":0.0000001,"icons":{}}`, "left is out of range"},
		{"zero default size", `{"prefix":"p","height":0,"icons":{}}`, "the default size must be positive"},
		{"negative icon width", `{"prefix":"p","icons":{"a":{"body":"","width":-1}}}`, "icon a needs a positive size"},
		{"trailing content", `{"prefix":"p","icons":{}} x`, "invalid JSON at byte 26: trailing content"},
		{"leading zero", `{"prefix":"p","width":016,"icons":{}}`, "invalid JSON at byte 23: expected ',' or '}'"},
		{"unpaired surrogate", `{"prefix":"\ud800","icons":{}}`, "invalid JSON at byte 17: unpaired surrogate"},
		{"bad escape", `{"prefix":"p\q","icons":{}}`, "invalid JSON at byte 14: invalid escape"},
		{"control character", "{\"prefix\":\"a\nb\",\"icons\":{}}", "invalid JSON at byte 13: control character in string"},
		{"trailing comma", `{"prefix":"p","icons":{},}`, "invalid JSON at byte 25: expected a member name"},
		{"nesting of 65 levels", nestedArrays(64), "invalid JSON at byte 81: nesting is too deep"},
	} {
		t.Run(c.name, func(t *testing.T) {
			_, err := Parse([]byte(c.data))
			format, ok := errors.AsType[*FormatError](err)
			if !ok || format.Reason != c.reason {
				t.Fatalf("err = %v; want reason %q", err, c.reason)
			}
		})
	}
}

func TestParsePackAccepts(t *testing.T) {
	for name, data := range map[string]string{
		"nesting of 64 levels": nestedArrays(63),
		"last duplicate wins":  `{"prefix":"","prefix":"p","icons":{}}`,
		"decimal size":         `{"prefix":"p","icons":{"a":{"body":"","width":16.5,"left":-3}}}`,
		"escaped prefix":       `{"prefix":"\u0070","icons":{}}`,
		"unknown members":      `{"prefix":"p","aliases":{},"icons":{}}`,
	} {
		t.Run(name, func(t *testing.T) {
			if _, err := Parse([]byte(data)); err != nil {
				t.Fatal(err)
			}
		})
	}
}
