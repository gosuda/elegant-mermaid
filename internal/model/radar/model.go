package radar

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/radar"
)

const (
	scale          = 1000
	wholeCap       = 1 << 32
	maxCanvasPx    = 65536
	maxTicks       = 32 * scale
	defaultTicks   = 5 * scale
	configKey      = "radar"
	tensionCeiling = scale
)

const (
	codeAxesRequired     = "radar/axes-required"
	codeMissingAxisEntry = "radar/missing-axis-entry"
	codeTicksClamped     = "radar/ticks-clamped"
	codeEmptyRange       = "radar/empty-range"
)

type Graticule uint8

const (
	GraticuleCircle Graticule = iota
	GraticulePolygon
)

func (g Graticule) String() string {
	if g == GraticulePolygon {
		return "polygon"
	}
	return "circle"
}

type ConfigEntry struct {
	Key   string
	Value int64
}

type Axis struct {
	Name  string
	Label string
	Span  source.Span
}

type Curve struct {
	Name       string
	Label      string
	Values     []int64
	Span       source.Span
	EntryCount int
	Positional bool
}

type Options struct {
	ShowLegend bool
	Ticks      int64
	HasMax     bool
	Max        int64
	Min        int64
	Graticule  Graticule
	MaxSpan    source.Span
	MinSpan    source.Span
}

type Model struct {
	HeaderSpan source.Span
	AccTitle   string
	AccDescr   string
	Title      string
	TitleSpan  source.Span
	Config     []ConfigEntry
	Axes       []Axis
	Curves     []Curve
	Options    Options
}

type resolver struct {
	model *Model
	diags []diag.Diagnostic
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{HeaderSpan: document.Header.Span, Options: Options{ShowLegend: true, Ticks: defaultTicks}}}
	r.readConfig(syntax.Preprocess(src))
	r.metadata(document)
	r.axes(document.Axes)
	for _, curve := range document.Curves {
		r.curve(curve)
	}
	r.options(document)
	r.checkRange(document.Header.Span)
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, r.diags
}

func (r *resolver) issue(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func (r *resolver) warn(code, message string, span source.Span) {
	d := syn.Diagnostic(code, message, span)
	d.Severity = diag.SeverityWarning
	r.diags = append(r.diags, d)
}

func (r *resolver) metadata(document *syn.Start) {
	if t := document.Title; t != nil && t.Value != "" {
		r.model.Title, r.model.TitleSpan = text(t.Value), t.Span
	}
	if t := document.AccTitle; t != nil && t.Value != "" {
		r.model.AccTitle = strings.TrimSpace(t.Value)
	}
	if t := document.AccDescr; t != nil && t.Value != "" {
		r.model.AccDescr = strings.TrimSpace(t.Value)
	}
}

func text(value string) string { return strings.TrimSpace(syntax.DecodeEntities(value)) }

func labelOf(name string, label *syn.Label) string {
	if label == nil {
		return name
	}
	return text(label.Value.Text)
}

func (r *resolver) axes(axes []syn.Axis) {
	for _, axis := range axes {
		r.model.Axes = append(r.model.Axes, Axis{Name: axis.Name.Text, Label: labelOf(axis.Name.Text, axis.Label), Span: axis.Span})
	}
}

func (r *resolver) curve(node syn.Curve) {
	curve := Curve{Name: node.Name.Text, Label: labelOf(node.Name.Text, node.Label), Span: node.Span, EntryCount: len(node.Entries), Positional: true}
	for _, entry := range node.Entries {
		if _, named := entry.Reference(); named {
			curve.Positional = false
			break
		}
	}
	if values, ok := r.values(node); ok {
		curve.Values = values
	}
	r.model.Curves = append(r.model.Curves, curve)
}

func (r *resolver) values(node syn.Curve) ([]int64, bool) {
	if len(node.Entries) == 0 {
		return nil, false
	}
	if _, keyed := node.Entries[0].Reference(); !keyed {
		values := make([]int64, len(node.Entries))
		for i, entry := range node.Entries {
			values[i] = Thousandths(entry.Number().Text)
		}
		return values, true
	}
	if len(r.model.Axes) == 0 {
		r.issue(codeAxesRequired, "keyed curve requires declared axes", node.Span)
		return nil, false
	}
	values := make([]int64, len(r.model.Axes))
	for i, axis := range r.model.Axes {
		at := slices.IndexFunc(node.Entries, func(e syn.Entry) bool {
			ref, keyed := e.Reference()
			return keyed && ref.Text == axis.Name
		})
		if at < 0 {
			r.issue(codeMissingAxisEntry, "missing entry for axis "+axis.Label, node.Span)
			return nil, false
		}
		values[i] = Thousandths(node.Entries[at].Number().Text)
	}
	return values, true
}

func (r *resolver) options(document *syn.Start) {
	o := &r.model.Options
	for _, option := range document.Options {
		value := option.Value
		switch option.Name.Kind {
		case "showLegend":
			o.ShowLegend = value.Text == "true"
		case "ticks":
			r.ticks(value)
		case "max":
			o.HasMax, o.Max, o.MaxSpan = true, Thousandths(value.Text), value.Span
		case "min":
			o.Min, o.MinSpan = Thousandths(value.Text), value.Span
		case "graticule":
			o.Graticule = graticuleOf(value.Text)
		}
	}
}

func graticuleOf(name string) Graticule {
	if name == "polygon" {
		return GraticulePolygon
	}
	return GraticuleCircle
}

func (r *resolver) ticks(value syn.Token) {
	ticks := Thousandths(value.Text)
	if ticks > maxTicks {
		r.warn(codeTicksClamped, "ticks "+value.Text+" exceeds 32; using 32", value.Span)
		ticks = maxTicks
	}
	r.model.Options.Ticks = ticks
}

func (r *resolver) checkRange(header source.Span) {
	o := r.model.Options
	high, found := o.Max, o.HasMax
	if !found {
		high, found = r.largestValue()
	}
	if !found || high > o.Min {
		return
	}
	span := header
	switch {
	case o.HasMax:
		span = o.MaxSpan
	case o.MinSpan != (source.Span{}):
		span = o.MinSpan
	}
	r.issue(codeEmptyRange, "radar maximum must be greater than minimum", span)
}

func (r *resolver) largestValue() (int64, bool) {
	var high int64
	found := false
	for _, curve := range r.model.Curves {
		for _, v := range curve.Values {
			if !found || v > high {
				high, found = v, true
			}
		}
	}
	return high, found
}

type intRange struct{ low, high int64 }

var integerKeys = map[string]intRange{
	"width":       {1, maxCanvasPx},
	"height":      {1, maxCanvasPx},
	"marginTop":   {0, maxCanvasPx},
	"marginRight": {0, maxCanvasPx},
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
		r.readRadar(block)
	}
}

func (r *resolver) readFrontTitle(root syntax.ConfigValue) {
	for _, entry := range root.Entries {
		if entry.Key == "title" && entry.Value.Kind == syntax.ValueString {
			r.model.Title = text(entry.Value.Text)
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

func (r *resolver) readRadar(block syntax.ConfigValue) {
	radar, ok := mapping(block, configKey)
	if !ok {
		return
	}
	for _, field := range radar.Entries {
		r.readField(field)
	}
}

func (r *resolver) readField(field syntax.ConfigEntry) {
	if field.Key == "curveTension" {
		r.readTension(field.Value)
		return
	}
	bounds, known := integerKeys[field.Key]
	if !known || field.Value.Kind != syntax.ValueInteger {
		return
	}
	n, err := strconv.ParseInt(field.Value.Text, 10, 64)
	if err == nil && n >= bounds.low && n <= bounds.high {
		r.upsert(field.Key, n)
	}
}

func (r *resolver) readTension(value syntax.ConfigValue) {
	if value.Kind != syntax.ValueInteger && value.Kind != syntax.ValueDecimal {
		return
	}
	if literal := value.Text; !strings.HasPrefix(literal, "-") {
		if t := Thousandths(literal); t <= tensionCeiling {
			r.upsert("curveTension", t)
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

func digitValue(c byte) int64 { return int64(c - '0') }

func Thousandths(literal string) int64 {
	whole, fraction, _ := strings.Cut(literal, ".")
	var value int64
	for i := range len(whole) {
		value = min(value*10+digitValue(whole[i]), wholeCap)
	}
	value *= scale
	var tail int64
	for i := range 4 {
		tail *= 10
		if i < len(fraction) {
			tail += digitValue(fraction[i])
		}
	}
	value += tail / 10
	if tail%10 >= 5 {
		value++
	}
	return value
}
