package svg

import (
	"fmt"
	"io"
	"strconv"
	"strings"
	"unicode"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

type TextMode uint8

const (
	TextFont TextMode = iota
	TextPaths
)

type Options struct {
	Theme, Background                              string
	Text                                           TextMode
	IDPrefix, Title, Description, Kind, FontFamily string
}
type ConfigError struct{ Reason string }

func (e *ConfigError) Error() string { return "svg: " + e.Reason }

type renderer struct {
	strings.Builder
	theme theme.Theme
	used  map[string]bool
}

func Write(w io.Writer, s scene.Scene, opts Options) error {
	if opts.Text != TextFont {
		return &ConfigError{"text paths are not supported"}
	}
	if !validPrefix(opts.IDPrefix) {
		return &ConfigError{"invalid ID prefix"}
	}
	r, bg, err := prepare(opts)
	if err != nil {
		return err
	}
	var body strings.Builder
	for i, g := range s.Groups {
		fmt.Fprintf(&body, "<g class='emd-%s' id='%sg%d'>\n", g.Role.String(), escape(opts.IDPrefix), i)
		for _, p := range g.Items {
			out, e := r.primitive(p)
			if e != nil {
				return e
			}
			body.WriteString(out)
		}
		body.WriteString("</g>\n")
	}
	width, height := number(int64(s.Canvas.W)), number(int64(s.Canvas.H))
	r.header(opts, width, height)
	r.WriteString("<style>\n.emd-bg{fill:" + bg + "}\n")
	if err := r.styles(); err != nil {
		return err
	}
	r.WriteString(".emd-t-title{font-weight:600}\n.emd-t-label{font-weight:600}\n.emd-t-body{font-weight:400}\n</style>\n")
	fmt.Fprintf(&r.Builder, "<rect class='emd-bg' x='0' y='0' width='%s' height='%s'/>\n", width, height)
	r.WriteString(body.String())
	r.WriteString("</svg>\n")
	_, err = io.WriteString(w, r.String())
	return err
}
func (r *renderer) header(opts Options, width, height string) {
	title := opts.Title
	if title == "" {
		title = "Mermaid " + opts.Kind + " diagram"
	}
	font := opts.FontFamily
	if font == "" {
		font = "Inter, 'Helvetica Neue', Arial, sans-serif"
	}
	fmt.Fprintf(&r.Builder, "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 %s %s' width='%s' height='%s' font-family='%s' role='graphics-document document' aria-roledescription='diagram' aria-labelledby='%stitle'", width, height, width, height, escape(font), opts.IDPrefix)
	if opts.Description != "" {
		fmt.Fprintf(&r.Builder, " aria-describedby='%sdesc'", opts.IDPrefix)
	}
	r.WriteString(">\n")
	fmt.Fprintf(&r.Builder, "<title id='%stitle'>%s</title>\n", opts.IDPrefix, escape(title))
	if opts.Description != "" {
		fmt.Fprintf(&r.Builder, "<desc id='%sdesc'>%s</desc>\n", opts.IDPrefix, escape(opts.Description))
	}
}
func validPrefix(s string) bool {
	if s == "" {
		return true
	}
	for i, c := range s {
		if c > 127 || !unicode.IsLetter(c) && (i == 0 || !unicode.IsDigit(c) && c != '_' && c != '-') {
			return false
		}
	}
	return true
}
func number(v int64) string {
	sign := ""
	if v < 0 {
		sign = "-"
		v = -v
	}
	h := (v*100 + 32) / 64
	out := strconv.FormatInt(h/100, 10)
	if h%100 != 0 {
		out += "." + strings.TrimRight(fmt.Sprintf("%02d", h%100), "0")
	}
	return sign + out
}
func escape(s string) string {
	var b strings.Builder
	for _, c := range s {
		switch c {
		case '&':
			b.WriteString("&amp;")
		case '<':
			b.WriteString("&lt;")
		case '>':
			b.WriteString("&gt;")
		case '"':
			b.WriteString("&quot;")
		case '\'':
			b.WriteString("&apos;")
		default:
			c = xmlRune(c)
			b.WriteRune(c)
		}
	}
	return b.String()
}
func xmlRune(c rune) rune {
	if c == '\n' || c == '\r' || c == '\t' {
		return c
	}
	if c < 32 || c == '\ufffe' || c == '\uffff' {
		return '\ufffd'
	}
	return c
}
func prepare(opts Options) (renderer, string, error) {
	t, err := theme.Resolve(opts.Theme)
	if err != nil {
		return renderer{}, "", err
	}
	bg := t.Colour(theme.Background).Hex()
	if opts.Background != "" {
		c, err := theme.ParseHex(opts.Background)
		if err != nil {
			return renderer{}, "", err
		}
		bg = c.Hex()
	}
	return renderer{theme: t, used: make(map[string]bool)}, bg, nil
}
func class(style string, n uint8) string {
	if strings.HasPrefix(style, "series") || style == "text-on-series" {
		return style + "-" + strconv.Itoa(int(n))
	}
	return style
}
func styleRow(name string) (gen.Style, error) {
	for _, s := range gen.Styles {
		if s.Name == name {
			return s, nil
		}
	}
	return gen.Style{}, &ConfigError{"unknown style " + name}
}
func colourToken(name string, n uint8) (theme.Token, error) {
	if name == "series" {
		return theme.Series0 + theme.Token(n%12), nil
	}
	for t := theme.Background; t <= theme.Success; t++ {
		if t.String() == name {
			return t, nil
		}
	}
	return 0, &ConfigError{"unknown colour token " + name}
}
func (r *renderer) fillColour(name string, n uint8) (string, error) {
	if name == "none" {
		return name, nil
	}
	token, err := colourToken(name, n)
	if err != nil {
		return "", err
	}
	return r.theme.Colour(token).Hex(), nil
}
func (r *renderer) strokeColour(name string, n uint8) (string, error) {
	if name == "none" {
		return name, nil
	}
	token, err := colourToken(name, n)
	if err != nil {
		return "", err
	}
	return r.theme.Colour(r.theme.Stroke(token)).Hex(), nil
}

var styleOrder = []string{"node", "group", "band", "note", "edge", "rule", "mark", "mark-hollow", "ink", "ink-line", "series", "series-line", "series-tint", "series-flow", "error", "warning", "success", "plate", "text", "text-muted", "text-inverse", "text-on-series"}

func (r *renderer) styles() error {
	for _, name := range styleOrder {
		for n := uint8(0); n < 12; n++ {
			key := class(name, n)
			if !r.used[key] {
				continue
			}
			row, e := styleRow(name)
			if e != nil {
				return e
			}
			if e = r.styleRule(key, row, n); e != nil {
				return e
			}
			if key == name {
				break
			}
		}
	}
	return nil
}
func (r *renderer) styleRule(key string, row gen.Style, n uint8) error {
	fill := row.Fill
	if fill == "on-series" {
		if r.theme.SeriesText(n) == 2 {
			return &ConfigError{"text-on-series requires plate"}
		}
		fill = "fg"
		if r.theme.SeriesText(n) == 1 {
			fill = "bg"
		}
	}
	f, e := r.fillColour(fill, n)
	if e != nil {
		return e
	}
	fmt.Fprintf(&r.Builder, ".emd-s-%s{fill:%s", key, f)
	if row.Class == 0 {
		s, e := r.strokeColour(row.Stroke, n)
		if e != nil {
			return e
		}
		r.WriteString(";stroke:" + s)
	}
	if row.Tint == 1 {
		r.WriteString(";fill-opacity:0.4")
	}
	if row.Tint == 2 {
		r.WriteString(";stroke-opacity:0.4")
	}
	r.WriteString("}\n")
	return nil
}
func (r *renderer) attributes(s scene.Shape) (string, error) {
	row, e := styleRow(s.Style)
	if e != nil {
		return "", e
	}
	key := class(s.Style, s.Series)
	r.used[key] = true
	out := "class='emd-s-" + key + "'"
	if row.Stroke != "none" {
		v := int64(64)
		switch s.Width.Kind {
		case scene.WidthEmphasis:
			v = 128
		case scene.WidthUnits:
			v = int64(s.Width.Units)
		}
		out += " stroke-width='" + number(v) + "'"
	}
	switch s.Line {
	case scene.LineDotted:
		out += " stroke-dasharray='3 3'"
	case scene.LineDashed:
		out += " stroke-dasharray='8 4'"
	}
	return out, nil
}
