package svg

import (
	"fmt"
	"io"
	"strconv"
	"strings"
	"unicode"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/interaction"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
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
	Look                                           scene.Look
	Links                                          []interaction.OwnerLink
	Outlines                                       *scenelink.Outlines
}
type ConfigError struct{ Reason string }

func (e *ConfigError) Error() string { return "svg: " + e.Reason }

type renderer struct {
	strings.Builder
	theme    theme.Theme
	used     map[string]bool
	look     scene.Look
	sketched sketchedClasses
	outlines *scenelink.Outlines
}

func Write(w io.Writer, s scene.Scene, opts Options) error {
	if err := validateText(opts); err != nil {
		return err
	}
	if !validPrefix(opts.IDPrefix) {
		return &ConfigError{"invalid ID prefix"}
	}
	r, bg, err := prepare(opts)
	if err != nil {
		return err
	}
	r.look = opts.Look
	if opts.Text == TextPaths {
		r.outlines = opts.Outlines
	}
	body, err := r.body(s, opts)
	if err != nil {
		return err
	}
	if err := r.document(s, opts, bg, body); err != nil {
		return err
	}
	_, err = io.WriteString(w, r.String())
	return err
}

func (r *renderer) body(s scene.Scene, opts Options) (string, error) {
	links := indexLinks(opts.Links)
	var body strings.Builder
	index := 0
	for i, g := range s.Groups {
		link, linked := links[linkKey{g.Owner, g.Role}]
		if linked {
			body.WriteString(link.open())
		}
		next, err := r.group(&body, g, i, index, opts.IDPrefix)
		if err != nil {
			return "", err
		}
		index = next
		if linked {
			body.WriteString("</a>\n")
		}
	}
	return body.String(), nil
}

func (r *renderer) group(body *strings.Builder, g *scene.Group, i, index int, idPrefix string) (int, error) {
	fmt.Fprintf(body, "<g class='emd-%s' id='%sg%d'>\n", g.Role.String(), escape(idPrefix), i)
	for _, p := range g.Items {
		out, err := r.primitive(p, index)
		index++
		if err != nil {
			return index, err
		}
		body.WriteString(out)
	}
	body.WriteString("</g>\n")
	return index, nil
}

func (r *renderer) document(s scene.Scene, opts Options, bg, body string) error {
	width, height := number(int64(s.Canvas.W)), number(int64(s.Canvas.H))
	r.header(opts, width, height)
	r.WriteString("<style>\n.emd-bg{fill:" + bg + "}\n")
	if err := r.styles(); err != nil {
		return err
	}
	r.WriteString(".emd-t-title{font-weight:600}\n.emd-t-label{font-weight:600}\n.emd-t-body{font-weight:400}\n")
	r.WriteString("</style>\n")
	fmt.Fprintf(&r.Builder, "<rect class='emd-bg' x='0' y='0' width='%s' height='%s'/>\n", width, height)
	r.WriteString(body)
	r.WriteString("</svg>\n")
	return nil
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

func styleName(i int) string {
	switch {
	case i < 6:
		return structuralStyleName(i)
	case i < 10:
		return symbolStyleName(i)
	case i < 14:
		return seriesStyleName(i)
	case i < 18:
		return surfaceStyleName(i)
	default:
		return textStyleName(i)
	}
}

func structuralStyleName(i int) string {
	switch i {
	case 0:
		return "node"
	case 1:
		return "group"
	case 2:
		return "band"
	case 3:
		return "note"
	case 4:
		return "edge"
	case 5:
		return "rule"
	default:
		panic("invalid structural style index")
	}
}

func symbolStyleName(i int) string {
	switch i {
	case 6:
		return "mark"
	case 7:
		return "mark-hollow"
	case 8:
		return "ink"
	case 9:
		return "ink-line"
	default:
		panic("invalid symbol style index")
	}
}

func seriesStyleName(i int) string {
	switch i {
	case 10:
		return "series"
	case 11:
		return "series-line"
	case 12:
		return "series-tint"
	case 13:
		return "series-flow"
	default:
		panic("invalid series style index")
	}
}

func surfaceStyleName(i int) string {
	switch i {
	case 14:
		return "error"
	case 15:
		return "warning"
	case 16:
		return "success"
	case 17:
		return "plate"
	default:
		panic("invalid surface style index")
	}
}

func textStyleName(i int) string {
	switch i {
	case 18:
		return "text"
	case 19:
		return "text-muted"
	case 20:
		return "text-inverse"
	case 21:
		return "text-on-series"
	default:
		panic("invalid text style index")
	}
}

func (r *renderer) styles() error {
	for i := range 22 {
		name := styleName(i)
		for n := range uint8(12) {
			key := class(name, n)
			if err := r.usedStyle(key, name, n, r.sketched[i][n]); err != nil {
				return err
			}
			if key == name {
				break
			}
		}
	}
	return nil
}

func (r *renderer) usedStyle(key, name string, n, flags uint8) error {
	if !r.used[key] && flags == 0 {
		return nil
	}
	row, err := styleRow(name)
	if err != nil {
		return err
	}
	if r.used[key] {
		if err := r.styleRule(key, row, n); err != nil {
			return err
		}
	}
	return r.sketchRules(key, row, n, flags)
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
		if row.Stroke != "none" {
			r.WriteString(";stroke-linecap:round;stroke-linejoin:round")
		}
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

func (r *renderer) shapeKey(s scene.Shape) (string, gen.Style, error) {
	row, e := styleRow(s.Style)
	if e != nil {
		return "", gen.Style{}, e
	}
	key := class(s.Style, s.Series)
	r.used[key] = true
	return key, row, nil
}

func (r *renderer) strokeAttributes(s scene.Shape, row gen.Style) string {
	out := ""
	if row.Stroke != "none" {
		v := int64(64)
		width := r.look.Width(s.Width)
		switch width.Kind {
		case scene.WidthEmphasis:
			v = 128
		case scene.WidthUnits:
			v = int64(width.Units)
		}
		out += " stroke-width='" + number(v) + "'"
	}
	switch s.Line {
	case scene.LineDotted:
		out += " stroke-dasharray='3 3'"
	case scene.LineDashed:
		out += " stroke-dasharray='8 4'"
	}
	return out
}
