package sequence

import (
	"slices"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

func asciiLower(text string) string {
	b := []byte(text)
	for i, c := range b {
		if c >= 'A' && c <= 'Z' {
			b[i] = c + 'a' - 'A'
		}
	}
	return string(b)
}

func labelText(token string) (string, Wrap) {
	text, wrap := stripWrapWith(strings.TrimPrefix(token, ":"))
	return syntax.DecodeEntities(strings.TrimSpace(text)), wrap
}

func stripWrap(token string) string {
	text, _ := stripWrapWith(token)
	return text
}

func stripWrapWith(token string) (string, Wrap) {
	body := strings.TrimLeft(token, " \t")
	folded := asciiLower(body)
	if strings.HasPrefix(folded, "nowrap:") {
		return body[len("nowrap:"):], WrapOff
	}
	if strings.HasPrefix(folded, "wrap:") {
		return body[len("wrap:"):], WrapOn
	}
	return body, WrapDefault
}

func textOverride(token string) Wrap {
	_, wrap := stripWrapWith(token)
	return wrap
}

func dottedArrow(kind string) bool {
	return strings.HasPrefix(kind, "DOTTED_") || strings.HasPrefix(kind, "BIDIRECTIONAL_DOTTED_") || strings.HasSuffix(kind, "_DOTTED")
}

var arrowHeads = map[string][2]string{
	"SOLID_ARROW":                       {"", "arrowhead"},
	"DOTTED_ARROW":                      {"", "arrowhead"},
	"BIDIRECTIONAL_SOLID_ARROW":         {"arrowhead", "arrowhead"},
	"BIDIRECTIONAL_DOTTED_ARROW":        {"arrowhead", "arrowhead"},
	"SOLID_OPEN_ARROW":                  {"", "none"},
	"DOTTED_OPEN_ARROW":                 {"", "none"},
	"SOLID_CROSS":                       {"", "crosshead"},
	"DOTTED_CROSS":                      {"", "crosshead"},
	"SOLID_POINT":                       {"", "filled-head"},
	"DOTTED_POINT":                      {"", "filled-head"},
	"SOLID_ARROW_TOP":                   {"", "solidTopArrowHead"},
	"SOLID_ARROW_TOP_DOTTED":            {"", "solidTopArrowHead"},
	"SOLID_ARROW_BOTTOM":                {"", "solidBottomArrowHead"},
	"SOLID_ARROW_BOTTOM_DOTTED":         {"", "solidBottomArrowHead"},
	"STICK_ARROW_TOP":                   {"", "stickTopArrowHead"},
	"STICK_ARROW_TOP_DOTTED":            {"", "stickTopArrowHead"},
	"STICK_ARROW_BOTTOM":                {"", "stickBottomArrowHead"},
	"STICK_ARROW_BOTTOM_DOTTED":         {"", "stickBottomArrowHead"},
	"SOLID_ARROW_TOP_REVERSE":           {"solidBottomArrowHead", ""},
	"SOLID_ARROW_TOP_REVERSE_DOTTED":    {"solidBottomArrowHead", ""},
	"SOLID_ARROW_BOTTOM_REVERSE":        {"solidTopArrowHead", ""},
	"SOLID_ARROW_BOTTOM_REVERSE_DOTTED": {"solidTopArrowHead", ""},
	"STICK_ARROW_TOP_REVERSE":           {"stickBottomArrowHead", ""},
	"STICK_ARROW_TOP_REVERSE_DOTTED":    {"stickBottomArrowHead", ""},
	"STICK_ARROW_BOTTOM_REVERSE":        {"stickTopArrowHead", ""},
	"STICK_ARROW_BOTTOM_REVERSE_DOTTED": {"stickTopArrowHead", ""},
}

func heads(kind string) (string, string) {
	pair := arrowHeads[kind]
	return pair[0], pair[1]
}

func splitLink(raw string) (string, string) {
	runes := []rune(raw)
	sep := slices.Index(runes, '@')
	end := sep - 1
	if end < 0 {
		end = max(len(runes)+end, 0)
	}
	return strings.TrimSpace(string(runes[:end])), strings.TrimSpace(string(runes[sep+1:]))
}

func boxColorLabel(raw string) (string, string, bool) {
	raw = strings.TrimSpace(raw)
	color, rest, ok := colorPrefix(raw)
	if !ok {
		return "", raw, false
	}
	return color, strings.TrimSpace(rest), true
}

func colorPrefix(raw string) (string, string, bool) {
	wordEnd := strings.IndexFunc(raw, func(c rune) bool {
		return c >= utf8.RuneSelf || !wordByte(byte(c))
	})
	if wordEnd < 0 {
		wordEnd = len(raw)
	}
	word := raw[:wordEnd]
	switch asciiLower(word) {
	case "rgb", "rgba", "hsl", "hsla":
		return colorFunction(raw, wordEnd)
	}
	if isNamedColor(word) {
		return word, raw[wordEnd:], true
	}
	return "", raw, false
}

func colorFunction(raw string, wordEnd int) (string, string, bool) {
	after := strings.TrimLeftFunc(raw[wordEnd:], isUnicodeSpace)
	body, ok := strings.CutPrefix(after, "(")
	if !ok {
		return "", raw, false
	}
	closeAt := strings.LastIndexByte(body, ')')
	if closeAt < 0 || !isColorArguments(body[:closeAt]) {
		return "", raw, false
	}
	consumed := len(raw) - len(body) + closeAt + 1
	return strings.TrimSpace(raw[:consumed]), raw[consumed:], true
}

func wordByte(c byte) bool {
	return c >= '0' && c <= '9' || c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' || c == '_'
}

func isUnicodeSpace(c rune) bool {
	return strings.TrimSpace(string(c)) == ""
}

func isColorArguments(arguments string) bool {
	if strings.TrimSpace(arguments) == "" {
		return false
	}
	for _, c := range arguments {
		switch {
		case c >= '0' && c <= '9', c >= 'a' && c <= 'z', c >= 'A' && c <= 'Z':
		case c == ' ', c == '\t', c == '\n', c == '\r', c == '\f':
		case strings.ContainsRune(",./%+-", c):
		default:
			return false
		}
	}
	return true
}

func isNamedColor(word string) bool {
	_, found := slices.BinarySearch(namedColors, asciiLower(word))
	return found
}

var namedColors = []string{
	"aliceblue", "antiquewhite", "aqua", "aquamarine", "azure", "beige", "bisque", "black", "blanchedalmond", "blue",
	"blueviolet", "brown", "burlywood", "cadetblue", "chartreuse", "chocolate", "coral", "cornflowerblue", "cornsilk",
	"crimson", "currentcolor", "cyan", "darkblue", "darkcyan", "darkgoldenrod", "darkgray", "darkgreen", "darkgrey",
	"darkkhaki", "darkmagenta", "darkolivegreen", "darkorange", "darkorchid", "darkred", "darksalmon", "darkseagreen",
	"darkslateblue", "darkslategray", "darkslategrey", "darkturquoise", "darkviolet", "deeppink", "deepskyblue",
	"dimgray", "dimgrey", "dodgerblue", "firebrick", "floralwhite", "forestgreen", "fuchsia", "gainsboro", "ghostwhite",
	"gold", "goldenrod", "gray", "green", "greenyellow", "grey", "honeydew", "hotpink", "indianred", "indigo", "ivory",
	"khaki", "lavender", "lavenderblush", "lawngreen", "lemonchiffon", "lightblue", "lightcoral", "lightcyan",
	"lightgoldenrodyellow", "lightgray", "lightgreen", "lightgrey", "lightpink", "lightsalmon", "lightseagreen",
	"lightskyblue", "lightslategray", "lightslategrey", "lightsteelblue", "lightyellow", "lime", "limegreen", "linen",
	"magenta", "maroon", "mediumaquamarine", "mediumblue", "mediumorchid", "mediumpurple", "mediumseagreen",
	"mediumslateblue", "mediumspringgreen", "mediumturquoise", "mediumvioletred", "midnightblue", "mintcream",
	"mistyrose", "moccasin", "navajowhite", "navy", "oldlace", "olive", "olivedrab", "orange", "orangered", "orchid",
	"palegoldenrod", "palegreen", "paleturquoise", "palevioletred", "papayawhip", "peachpuff", "peru", "pink", "plum",
	"powderblue", "purple", "rebeccapurple", "red", "rosybrown", "royalblue", "saddlebrown", "salmon", "sandybrown",
	"seagreen", "seashell", "sienna", "silver", "skyblue", "slateblue", "slategray", "slategrey", "snow", "springgreen",
	"steelblue", "tan", "teal", "thistle", "tomato", "transparent", "turquoise", "violet", "wheat", "white", "whitesmoke",
	"yellow", "yellowgreen",
}
