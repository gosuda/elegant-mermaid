package icon

import (
	"fmt"
	"strings"
	"unicode/utf8"
)

type FormatError struct{ Reason string }

func (e *FormatError) Error() string { return "malformed icon pack: " + e.Reason }

func malformed(format string, args ...any) error {
	return &FormatError{Reason: fmt.Sprintf(format, args...)}
}

const maxDimensionDigits = 6

const defaultSize = 16 * fixedScale

type Pack struct {
	Prefix string
	icons  map[string]*Icon
}

type Icon struct {
	width, height, left, top int64
	paths                    [][]command
	supported                bool
}

type box struct{ left, top, width, height int64 }

func Parse(data []byte) (*Pack, error) {
	root, err := readRoot(data)
	if err != nil {
		return nil, err
	}
	prefix, icons, err := rootMembers(root)
	if err != nil {
		return nil, err
	}
	defaults, err := packDefaults(root)
	if err != nil {
		return nil, err
	}
	pack := &Pack{Prefix: prefix, icons: make(map[string]*Icon, len(icons.members))}
	for _, member := range icons.members {
		icon, err := buildIcon(member.key, member.value, defaults)
		if err != nil {
			return nil, err
		}
		pack.icons[member.key] = icon
	}
	return pack, nil
}

func readRoot(data []byte) (*jsonValue, error) {
	if !utf8.Valid(data) {
		return nil, malformed("invalid UTF-8")
	}
	root, err := parseJSON(string(data))
	if err != nil {
		return nil, &FormatError{err.Error()}
	}
	if root.kind != jsonObject {
		return nil, malformed("the root must be an object")
	}
	return root, nil
}

func rootMembers(root *jsonValue) (string, *jsonValue, error) {
	prefix := root.member("prefix")
	if prefix == nil || prefix.kind != jsonString {
		return "", nil, malformed("missing string prefix")
	}
	if prefix.text == "" {
		return "", nil, malformed("the prefix must not be empty")
	}
	icons := root.member("icons")
	if icons == nil || icons.kind != jsonObject {
		return "", nil, malformed("missing icons object")
	}
	return prefix.text, icons, nil
}

func packDefaults(root *jsonValue) (box, error) {
	var defaults box
	var err error
	for _, field := range []struct {
		key      string
		fallback int64
		target   *int64
	}{
		{"left", 0, &defaults.left},
		{"top", 0, &defaults.top},
		{"width", defaultSize, &defaults.width},
		{"height", defaultSize, &defaults.height},
	} {
		if *field.target, err = dimension(root, field.key, field.fallback); err != nil {
			return box{}, err
		}
	}
	if defaults.width <= 0 || defaults.height <= 0 {
		return box{}, malformed("the default size must be positive")
	}
	return defaults, nil
}

func buildIcon(name string, entry *jsonValue, defaults box) (*Icon, error) {
	if entry.kind != jsonObject {
		return nil, malformed("icon %s must be an object", name)
	}
	body := entry.member("body")
	if body == nil || body.kind != jsonString {
		return nil, malformed("icon %s needs a string body", name)
	}
	own, err := iconBox(name, entry, defaults)
	if err != nil {
		return nil, err
	}
	icon := &Icon{width: own.width, height: own.height, left: own.left, top: own.top}
	icon.paths, icon.supported = parseBody(body.text)
	icon.supported = icon.supported && max(icon.width, icon.height) >= fixedScale
	return icon, nil
}

func iconBox(name string, entry *jsonValue, defaults box) (box, error) {
	var own box
	var err error
	if own.width, err = dimension(entry, "width", defaults.width); err != nil {
		return box{}, err
	}
	if own.height, err = dimension(entry, "height", defaults.height); err != nil {
		return box{}, err
	}
	if own.width <= 0 || own.height <= 0 {
		return box{}, malformed("icon %s needs a positive size", name)
	}
	if own.left, err = dimension(entry, "left", defaults.left); err != nil {
		return box{}, err
	}
	if own.top, err = dimension(entry, "top", defaults.top); err != nil {
		return box{}, err
	}
	return own, nil
}

func dimension(owner *jsonValue, key string, fallback int64) (int64, error) {
	value := owner.member(key)
	switch {
	case value == nil:
		return fallback, nil
	case value.kind != jsonNumber:
		return 0, malformed("%s must be a number", key)
	}
	number, ok := dimensionValue(value.text)
	if !ok {
		return 0, malformed("%s is out of range", key)
	}
	return number, nil
}

func dimensionValue(text string) (int64, bool) {
	if strings.ContainsAny(text, "eE") {
		return 0, false
	}
	whole, fraction, _ := strings.Cut(strings.TrimPrefix(text, "-"), ".")
	if len(whole) > maxDimensionDigits || len(fraction) > maxDimensionDigits {
		return 0, false
	}
	return parseDecimal(text)
}

func (p *Pack) lookup(name string) (*Icon, bool) {
	icon, ok := p.icons[name]
	return icon, ok
}

const asciiSpace = " \t\r\n\f"

func parseBody(body string) ([][]command, bool) {
	var paths [][]command
	rest := strings.Trim(body, asciiSpace)
	for rest != "" {
		d, tail, ok := nextPath(rest)
		if !ok {
			return nil, false
		}
		commands, ok := parsePath(d)
		if !ok {
			return nil, false
		}
		paths = append(paths, commands)
		rest = strings.Trim(tail, asciiSpace)
	}
	return paths, true
}

func nextPath(s string) (string, string, bool) {
	rest, ok := strings.CutPrefix(s, "<path")
	if !ok || rest == "" || !isSpace(rest[0]) {
		return "", "", false
	}
	d := ""
	hasD := false
	for {
		rest = strings.TrimLeft(rest, " \t\r\n\f")
		if tail, closed := closeTag(rest); closed {
			return d, tail, hasD
		}
		name, value, tail, ok := nextAttribute(rest)
		if !ok || !acceptAttribute(name, value) {
			return "", "", false
		}
		if name == "d" {
			d, hasD = value, true
		}
		rest = tail
	}
}

func closeTag(s string) (string, bool) {
	if tail, ok := strings.CutPrefix(s, "/>"); ok {
		return tail, true
	}
	if tail, ok := strings.CutPrefix(s, "></path>"); ok {
		return tail, true
	}
	return "", false
}

func acceptAttribute(name, value string) bool {
	return name == "d" || name == "fill" && value == "currentColor"
}

func nextAttribute(s string) (name, value, rest string, ok bool) {
	name, rest, ok = strings.Cut(s, "=")
	if !ok || name == "" || strings.ContainsAny(name, " \t\r\n\f<>/\"'") || rest == "" {
		return "", "", "", false
	}
	quote := rest[0]
	if quote != '"' && quote != '\'' {
		return "", "", "", false
	}
	value, rest, ok = strings.Cut(rest[1:], string(quote))
	return name, value, rest, ok
}
