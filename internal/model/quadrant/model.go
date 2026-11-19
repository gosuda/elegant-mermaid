package quadrant

import (
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/quadrant"
)

const (
	scale         = 1000
	configKey     = "quadrantChart"
	NoRadius      = -1
	maxRadius     = 4096
	maxPixels     = 65536
	maxSmallPx    = 1024
	maxFontPx     = 256
	delimiterTail = " ⟶ "
)

type ConfigEntry struct {
	Key   string
	Value int64
}

type Point struct {
	Text        string
	LabelKey    string
	LabelSpan   source.Span
	Class       string
	X, Y        int64
	Radius      int64
	Color       string
	StrokeColor string
	StrokeWidth string
	Span        source.Span
}

type QuadrantDeclaration struct {
	Number int
	Span   source.Span
}

type Model struct {
	HeaderSpan           source.Span
	HasXAxis             bool
	HasYAxis             bool
	QuadrantDeclarations []QuadrantDeclaration
	AccTitle             string
	AccDescr             string
	Title                string
	TitleSpan            source.Span
	Quadrants            [4]string
	XLeft                string
	XRight               string
	YBottom              string
	YTop                 string
	Points               []Point
	Config               []ConfigEntry
}

const (
	hasRadius uint8 = 1 << iota
	hasColor
	hasStrokeColor
	hasStrokeWidth
)

type styleSet struct {
	has         uint8
	radius      int64
	color       string
	strokeColor string
	strokeWidth string
}

func (s styleSet) over(base styleSet) styleSet {
	out := base
	if s.has&hasRadius != 0 {
		out.has |= hasRadius
		out.radius = s.radius
	}
	if s.has&hasColor != 0 {
		out.has |= hasColor
		out.color = s.color
	}
	if s.has&hasStrokeColor != 0 {
		out.has |= hasStrokeColor
		out.strokeColor = s.strokeColor
	}
	if s.has&hasStrokeWidth != 0 {
		out.has |= hasStrokeWidth
		out.strokeWidth = s.strokeWidth
	}
	return out
}

type resolver struct {
	text    string
	model   *Model
	diags   []diag.Diagnostic
	classes map[string]styleSet
	inline  []styleSet
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{text: string(src), model: &Model{HeaderSpan: document.Header.Span}, classes: map[string]styleSet{}}
	r.readConfig(syntax.Preprocess(src))
	for _, line := range document.Document.Lines {
		r.statement(line.Statement.Kind)
	}
	r.applyClasses()
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, r.diags
}

func (r *resolver) applyClasses() {
	for i := range r.model.Points {
		p := &r.model.Points[i]
		styles := r.inline[i]
		if class, ok := r.classes[p.Class]; ok && p.Class != "" {
			styles = styles.over(class)
		}
		p.Radius = NoRadius
		if styles.has&hasRadius != 0 {
			p.Radius = styles.radius
		}
		p.Color, p.StrokeColor, p.StrokeWidth = styles.color, styles.strokeColor, styles.strokeWidth
	}
}

type intRange struct{ low, high int64 }

var integerKeys = map[string]intRange{
	"chartWidth":         {1, maxPixels},
	"chartHeight":        {1, maxPixels},
	"quadrantPadding":    {0, maxSmallPx},
	"titlePadding":       {0, maxSmallPx},
	"titleFontSize":      {1, maxFontPx},
	"xAxisLabelPadding":  {0, maxSmallPx},
	"yAxisLabelPadding":  {0, maxSmallPx},
	"xAxisLabelFontSize": {1, maxFontPx},
	"yAxisLabelFontSize": {1, maxFontPx},
	"pointRadius":        {0, maxRadius},
	"pointTextPadding":   {0, maxSmallPx},
}

func (r *resolver) readConfig(pre syntax.Preprocessed) {
	if pre.HasFront {
		r.readFrontTitle(pre.Root)
	}
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		r.readChart(block)
	}
}

func (r *resolver) readFrontTitle(root syntax.ConfigValue) {
	for _, entry := range root.Entries {
		if entry.Key == "title" && entry.Value.Kind == syntax.ValueString {
			r.model.Title = sanitize(entry.Value.Text)
		}
	}
}

func mapping(value syntax.ConfigValue, key string) (syntax.ConfigValue, bool) {
	if value.Kind != syntax.ValueMapping {
		return syntax.ConfigValue{}, false
	}
	i := slices.IndexFunc(value.Entries, func(e syntax.ConfigEntry) bool { return e.Key == key })
	if i < 0 || value.Entries[i].Value.Kind != syntax.ValueMapping {
		return syntax.ConfigValue{}, false
	}
	return value.Entries[i].Value, true
}

func (r *resolver) readChart(block syntax.ConfigValue) {
	chart, ok := mapping(block, configKey)
	if !ok {
		return
	}
	for _, field := range chart.Entries {
		bounds, known := integerKeys[field.Key]
		if !known || field.Value.Kind != syntax.ValueInteger {
			continue
		}
		n, err := strconv.ParseInt(field.Value.Text, 10, 64)
		if err == nil && n >= bounds.low && n <= bounds.high {
			r.upsert(field.Key, n)
		}
	}
}

func (r *resolver) upsert(key string, value int64) {
	if i := slices.IndexFunc(r.model.Config, func(e ConfigEntry) bool { return e.Key == key }); i >= 0 {
		r.model.Config[i].Value = value
		return
	}
	r.model.Config = append(r.model.Config, ConfigEntry{Key: key, Value: value})
}

func jsSpace(r rune) bool {
	switch r {
	case '\t', '\n', '\v', '\f', '\r', ' ', 0xa0, 0x1680, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff:
		return true
	}
	return r >= 0x2000 && r <= 0x200a
}

func sanitize(text string) string { return syntax.DecodeEntities(strings.TrimFunc(text, jsSpace)) }

func (r *resolver) statement(kind syn.StatementKind) {
	switch s := kind.(type) {
	case *syn.Title:
		r.model.Title, r.model.TitleSpan = sanitize(s.Value.Text), s.Span
	case *syn.Accessibility:
		value := strings.TrimFunc(s.Value.Text, jsSpace)
		if s.Title {
			r.model.AccTitle = value
		} else {
			r.model.AccDescr = value
		}
	case *syn.AxisDetails:
		r.axis(s)
	case *syn.QuadrantDetails:
		r.model.QuadrantDeclarations = append(r.model.QuadrantDeclarations, QuadrantDeclaration{Number: s.Number, Span: s.Span})
		r.model.Quadrants[s.Number-1] = sanitize(s.Text.Value)
	case *syn.ClassDefStatement:
		r.classes[s.Name.Text] = r.parseStyles(s.Styles.Styles)
	case *syn.Points:
		r.point(s)
	}
}

func (r *resolver) axis(s *syn.AxisDetails) {
	if s.Y {
		r.model.HasYAxis = true
	} else {
		r.model.HasXAxis = true
	}
	first := s.First.Value
	if s.Delimiter != nil && s.Second == nil {
		first += delimiterTail
	}
	low, high := &r.model.XLeft, &r.model.XRight
	if s.Y {
		low, high = &r.model.YBottom, &r.model.YTop
	}
	*low = sanitize(first)
	if s.Second != nil {
		*high = sanitize(s.Second.Value)
	}
}

func (r *resolver) point(s *syn.Points) {
	var styles styleSet
	if s.Styles != nil {
		styles = r.parseStyles(s.Styles.Styles)
	}
	point := Point{Text: sanitize(s.Text.Value), LabelKey: s.Text.Value, LabelSpan: s.Text.Span, X: coordinate(s.PointX.Text), Y: coordinate(s.PointY.Text), Span: s.Span}
	if s.Class != nil {
		point.Class = s.Class.Text
	}
	r.model.Points = append(r.model.Points, point)
	r.inline = append(r.inline, styles)
}

func coordinate(lexeme string) int64 {
	if lexeme == "" || lexeme[0] == '1' {
		return scale
	}
	_, size := utf8.DecodeRuneInString(lexeme[1:])
	digits := lexeme[1+size:]
	var tail int64
	for i := range 4 {
		tail *= 10
		if i < len(digits) {
			tail += int64(digits[i] - '0')
		}
	}
	value := tail / 10
	if tail%10 >= 5 {
		value++
	}
	return value
}

type styleEntry struct {
	key, value         string
	keySpan, valueSpan source.Span
	hasValue           bool
}

func splitStyle(style syn.Style) styleEntry {
	trimmed := strings.TrimFunc(style.Text, jsSpace)
	start := style.Span.Start + len(style.Text) - len(strings.TrimLeftFunc(style.Text, jsSpace))
	colon := strings.IndexByte(trimmed, ':')
	if colon < 0 {
		return styleEntry{key: trimmed, keySpan: source.Span{Start: start, End: start + len(trimmed)}, valueSpan: source.Span{Start: start + len(trimmed), End: start + len(trimmed)}}
	}
	key := strings.TrimRightFunc(trimmed[:colon], jsSpace)
	rest := trimmed[colon+1:]
	lead := len(rest) - len(strings.TrimLeftFunc(rest, jsSpace))
	value := rest[lead:]
	if next := strings.IndexByte(value, ':'); next >= 0 {
		value = strings.TrimRightFunc(value[:next], jsSpace)
	}
	valueStart := start + colon + 1 + lead
	return styleEntry{
		key: key, keySpan: source.Span{Start: start, End: start + len(key)},
		value: value, valueSpan: source.Span{Start: valueStart, End: valueStart + len(value)}, hasValue: true,
	}
}

func (e styleEntry) shown() string {
	if !e.hasValue {
		return "undefined"
	}
	return e.value
}

func allDigits(s string) bool {
	return s != "" && !strings.ContainsFunc(s, func(r rune) bool { return r < '0' || r > '9' })
}

func hexColor(s string) bool {
	digits := strings.TrimPrefix(s, "#")
	if len(digits) != 3 && len(digits) != 6 {
		return false
	}
	return !strings.ContainsFunc(digits, func(r rune) bool {
		return (r < '0' || r > '9') && (r < 'a' || r > 'f') && (r < 'A' || r > 'F')
	})
}

func pixels(s string) bool {
	digits, ok := strings.CutSuffix(s, "px")
	return ok && allDigits(digits)
}

type styleRule struct {
	code, key, expectation string
	valid                  func(string) bool
	apply                  func(*styleSet, string)
}

var styleRules = map[string]styleRule{
	"radius": {"quadrant/invalid-radius", "radius", "number", allDigits, func(s *styleSet, v string) {
		radius, err := strconv.ParseInt(v, 10, 64)
		if err != nil || radius > maxRadius {
			radius = maxRadius
		}
		s.has |= hasRadius
		s.radius = radius
	}},
	"color": {"quadrant/invalid-color", "color", "hex code", hexColor, func(s *styleSet, v string) {
		s.has |= hasColor
		s.color = v
	}},
	"stroke-color": {"quadrant/invalid-stroke-color", "stroke-color", "hex code", hexColor, func(s *styleSet, v string) {
		s.has |= hasStrokeColor
		s.strokeColor = v
	}},
	"stroke-width": {"quadrant/invalid-stroke-width", "stroke-width", "number of pixels (eg. 10px)", pixels, func(s *styleSet, v string) {
		s.has |= hasStrokeWidth
		s.strokeWidth = v
	}},
}

func (r *resolver) parseStyles(styles []syn.Style) styleSet {
	var out styleSet
	for _, style := range styles {
		e := splitStyle(style)
		rule, known := styleRules[e.key]
		switch {
		case !known:
			r.diags = append(r.diags, syn.Diagnostic("quadrant/unsupported-style", "style named "+e.key+" is not supported.", e.keySpan))
		case !e.hasValue || !rule.valid(e.value):
			message := "value for " + rule.key + " " + e.shown() + " is invalid, please use a valid " + rule.expectation
			r.diags = append(r.diags, syn.Diagnostic(rule.code, message, e.valueSpan))
		default:
			rule.apply(&out, e.value)
		}
	}
	return out
}
