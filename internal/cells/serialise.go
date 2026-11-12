package cells

import "strings"

func cellText(v Cell, charset Charset) string {
	switch {
	case v.Cont:
		return ""
	case v.Label != "":
		return terminalText(v.Label)
	case v.Symbol != 0:
		return terminalText(string(v.Symbol))
	case v.Mask != 0:
		return string(Glyph(charset, v.Style, v.Mask))
	default:
		return string(BrailleGlyph(charset, v.Dots))
	}
}
func (c *Canvas) Serialise(charset Charset, mode ColorMode, lookup ColourLookup) []byte {
	var out strings.Builder
	for row := 0; row < c.H; row++ {
		c.writeRow(&out, row, charset, mode, lookup)
	}
	return []byte(out.String())
}
func (c *Canvas) writeRow(out *strings.Builder, row int, charset Charset, mode ColorMode, lookup ColourLookup) {
	end := c.W
	for end > 0 && cellText(c.cells[row*c.W+end-1], charset) == " " {
		end--
	}
	current := TokenFG
	for x := 0; x < end; x++ {
		v := c.cells[row*c.W+x]
		text := cellText(v, charset)
		token := v.colourToken()
		if mode != ColorNone && text != "" && text != " " && token != current {
			out.WriteString(SGR(mode, token, lookup))
			current = token
		}
		out.WriteString(text)
	}
	if mode != ColorNone && current != TokenFG {
		out.WriteString("\x1b[39m")
	}
	out.WriteByte('\n')
}

func (v Cell) colourToken() Token {
	token := v.Ink
	if v.Label != "" {
		token = v.LabelInk
	}
	if token == TokenBG {
		return TokenFG
	}
	return token
}

func terminalText(text string) string {
	first := strings.IndexFunc(text, terminalControl)
	if first < 0 {
		return text
	}
	var out strings.Builder
	out.Grow(len(text))
	out.WriteString(text[:first])
	for _, r := range text[first:] {
		if terminalControl(r) {
			r = '\uFFFD'
		}
		out.WriteRune(r)
	}
	return out.String()
}

func terminalControl(r rune) bool {
	return r < 0x20 || (r >= 0x7F && r <= 0x9F)
}
