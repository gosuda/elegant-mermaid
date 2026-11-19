package xychart

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/xychart"
)

const (
	scale        = 1000
	wholeCap     = 1 << 32
	NoSlot       = -1
	configKey    = "xyChart"
	horizontalID = "horizontal"
	maxCanvasPx  = 65536
)

type Orientation uint8

const (
	Vertical Orientation = iota
	Horizontal
)

func (o Orientation) String() string {
	if o == Horizontal {
		return horizontalID
	}
	return "vertical"
}

type DumpKind uint8

const (
	DumpBool DumpKind = iota
	DumpInteger
)

type DumpValue struct {
	Kind    DumpKind
	Bool    bool
	Integer int64
}

type ConfigEntry struct {
	Key   string
	Value DumpValue
}

type Point struct {
	Present bool
	Slot    int
	HasX    bool
	X       int64
	Y       int64
	Label   string
	Span    source.Span
}

type Plot struct {
	Line          bool
	Title         string
	Span          source.Span
	RawPointCount int
	Points        []Point
}

type Axis struct {
	Title      string
	Span       source.Span
	Categories []string
	Spans      []source.Span
	Min, Max   int64
	Band       bool
}

type Model struct {
	HeaderSpan  source.Span
	AccTitle    string
	AccDescr    string
	Title       string
	TitleSpan   source.Span
	Orientation Orientation
	Config      []ConfigEntry
	X           Axis
	Y           Axis
	Plots       []Plot
}

type placement struct {
	band  bool
	names []string
	xs    []int64
}

type resolver struct {
	model     *Model
	xSet      bool
	ySet      bool
	yObserved bool
	placed    []placement
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{X: Axis{Band: true}}}
	if len(document.Headers) > 0 {
		r.model.HeaderSpan = document.Headers[0].Keyword.Span
	}
	r.readConfig(syntax.Preprocess(src))
	for _, header := range document.Headers {
		if header.Orientation != nil {
			r.model.Orientation = orientationOf(header.Orientation.Text)
		}
	}
	for _, statement := range document.Document.Statements {
		r.statement(statement.Kind)
	}
	r.bindPlacements()
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, nil
}

func orientationOf(text string) Orientation {
	if text == horizontalID {
		return Horizontal
	}
	return Vertical
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
			r.model.Title = strings.TrimSpace(syntax.DecodeEntities(entry.Value.Text))
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

type intRange struct{ low, high int64 }

var integerKeys = map[string]intRange{
	"width":                    {1, maxCanvasPx},
	"height":                   {1, maxCanvasPx},
	"plotReservedSpacePercent": {30, 100},
}

func (r *resolver) readChart(block syntax.ConfigValue) {
	chart, ok := mapping(block, configKey)
	if !ok {
		return
	}
	for _, field := range chart.Entries {
		r.readField(field)
	}
	if axis, ok := mapping(chart, "xAxis"); ok {
		for _, field := range axis.Entries {
			r.readAxisField(field)
		}
	}
}

func integer(value syntax.ConfigValue, bounds intRange) (int64, bool) {
	if value.Kind != syntax.ValueInteger {
		return 0, false
	}
	n, err := strconv.ParseInt(value.Text, 10, 64)
	return n, err == nil && n >= bounds.low && n <= bounds.high
}

func (r *resolver) readField(field syntax.ConfigEntry) {
	if field.Key == "chartOrientation" && field.Value.Kind == syntax.ValueString {
		r.model.Orientation = orientationOf(field.Value.Text)
		return
	}
	bounds, known := integerKeys[field.Key]
	if !known {
		return
	}
	if n, ok := integer(field.Value, bounds); ok {
		r.upsert(field.Key, DumpValue{Kind: DumpInteger, Integer: n})
	}
}

func (r *resolver) readAxisField(field syntax.ConfigEntry) {
	switch field.Key {
	case "labelFontSize":
		if n, ok := integer(field.Value, intRange{1, 256}); ok {
			r.upsert("xAxis.labelFontSize", DumpValue{Kind: DumpInteger, Integer: n})
		}
	case "showLabel":
		if field.Value.Kind == syntax.ValueBool {
			r.upsert("xAxis.showLabel", DumpValue{Kind: DumpBool, Bool: field.Value.Bool})
		}
	}
}

func (r *resolver) upsert(key string, value DumpValue) {
	if i := slices.IndexFunc(r.model.Config, func(e ConfigEntry) bool { return e.Key == key }); i >= 0 {
		r.model.Config[i].Value = value
		return
	}
	r.model.Config = append(r.model.Config, ConfigEntry{Key: key, Value: value})
}

func text(t syn.Text) string { return strings.TrimSpace(syntax.DecodeEntities(t.Value)) }

func (r *resolver) statement(kind syn.StatementKind) {
	switch s := kind.(type) {
	case *syn.Title:
		r.model.Title, r.model.TitleSpan = text(s.Text), s.Span
	case *syn.Accessibility:
		value := strings.TrimSpace(s.Value.Text)
		if s.Title {
			r.model.AccTitle = value
		} else {
			r.model.AccDescr = value
		}
	case *syn.AxisStatement:
		r.axis(s)
	case *syn.PlotStatement:
		r.plot(s)
	}
}

func (r *resolver) axis(s *syn.AxisStatement) {
	axis := &r.model.X
	if s.Y {
		axis = &r.model.Y
	}
	title := ""
	if s.Title != nil {
		title = text(*s.Title)
	}
	switch {
	case s.Band != nil:
		axis.Band, axis.Categories, axis.Spans = true, nil, nil
		for _, c := range s.Band.Categories {
			axis.Categories = append(axis.Categories, text(c))
			axis.Spans = append(axis.Spans, c.Span)
		}
		r.xSet = true
	case s.Range != nil:
		axis.Band, axis.Categories, axis.Spans = false, nil, nil
		axis.Min, axis.Max = Thousandths(s.Range.Min.Text), Thousandths(s.Range.Max.Text)
		if s.Y {
			r.ySet, r.yObserved = true, true
		} else {
			r.xSet = true
		}
	}
	axis.Title, axis.Span = title, s.Span
}

func (r *resolver) plot(s *syn.PlotStatement) {
	values := make([]int64, len(s.Data.Points))
	for i, point := range s.Data.Points {
		values[i] = Thousandths(point.Number.Text)
	}
	m := r.model
	if !r.xSet {
		m.X = Axis{Title: m.X.Title, Span: m.X.Span, Min: scale, Max: int64(len(values)) * scale}
		r.xSet = true
	}
	kept := len(values)
	if m.X.Band {
		kept = min(kept, len(m.X.Categories))
	}
	if !r.ySet {
		r.observe(values[:kept])
	}
	plot := Plot{Line: s.Line, Span: s.Span, RawPointCount: len(values)}
	if s.Title != nil {
		plot.Title = text(*s.Title)
	}
	slots := kept
	if m.X.Band {
		slots = len(m.X.Categories)
	}
	placed := placement{band: m.X.Band}
	for i := range slots {
		p := plotPoint(s, values, i, kept)
		plot.Points = append(plot.Points, p)
		if m.X.Band {
			placed.names = append(placed.names, m.X.Categories[i])
		} else {
			placed.xs = append(placed.xs, linearX(m.X, i, slots))
		}
	}
	m.Plots = append(m.Plots, plot)
	r.placed = append(r.placed, placed)
}

func plotPoint(s *syn.PlotStatement, values []int64, i, kept int) Point {
	p := Point{Span: s.Span, Slot: NoSlot}
	if i < kept {
		p.Present, p.Y, p.Span = true, values[i], s.Data.Points[i].Span
		if s.Data.Points[i].Label != nil && s.Line {
			p.Label = text(*s.Data.Points[i].Label)
		}
	}
	return p
}

func linearX(axis Axis, index, count int) int64 {
	if count < 2 {
		return axis.Min
	}
	return axis.Min + geom.FloorDiv(int64(index)*(axis.Max-axis.Min), int64(count-1))
}

func (r *resolver) observe(values []int64) {
	for _, v := range values {
		if !r.yObserved {
			r.model.Y.Min, r.model.Y.Max, r.yObserved = v, v, true
			continue
		}
		r.model.Y.Min, r.model.Y.Max = min(r.model.Y.Min, v), max(r.model.Y.Max, v)
	}
}

func (r *resolver) bindPlacements() {
	x := r.model.X
	for i := range r.model.Plots {
		placed := r.placed[i]
		for j := range r.model.Plots[i].Points {
			p := &r.model.Plots[i].Points[j]
			switch {
			case placed.band && x.Band:
				p.Slot = slices.Index(x.Categories, placed.names[j])
			case !placed.band && !x.Band:
				p.HasX, p.X = true, placed.xs[j]
			}
		}
	}
}

func digitValue(c byte) int64 { return int64(c - '0') }

func Thousandths(literal string) int64 {
	negative := strings.HasPrefix(literal, "-")
	whole, fraction, _ := strings.Cut(strings.TrimLeft(literal, "+-"), ".")
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
	if negative {
		return -value
	}
	return value
}
