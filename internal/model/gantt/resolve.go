package gantt

import (
	"slices"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/civil"
	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/interaction"
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
)

const (
	codeUnsafeURL       = "interaction/unsafe-url"
	codeCallbackIgnored = "interaction/callback-ignored"
	codeToday           = "gantt/today-marker-ignored"
	codeTickUnsupported = "gantt/tick-interval-unsupported"
	codeAxisUnsupported = "gantt/axis-format-unsupported"
)

type resolver struct {
	model   *Model
	ids     map[string]int
	diags   []diag.Diagnostic
	lastID  string
	hasLast bool
	counter int
	order   int
	scans   scanState
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{Weekday: DefaultWeekday, Weekend: DefaultWeekend}, ids: map[string]int{}}
	r.readConfig(syntax.Preprocess(src))
	for _, line := range document.Document.Lines {
		if line.Statement != nil {
			r.statement(*line.Statement)
		}
	}
	r.finishDirectives()
	r.compile()
	slices.SortFunc(r.model.Config, func(a, b chartmodel.ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, r.diags
}

func trim(text string) string { return strings.TrimFunc(text, syn.IsSpace) }

func label(text string) string { return syntax.DecodeEntities(trim(text)) }

func (r *resolver) report(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func (r *resolver) statement(s syn.Statement) {
	if r.setting(s.Kind) || r.calendar(s) || r.text(s.Kind) {
		return
	}
	switch node := s.Kind.(type) {
	case *syn.Section:
		r.addSection(node.Token)
	case *syn.ClickStatement:
		r.click(node, s.Span)
	case *syn.Task:
		r.addTask(node, s.Span)
	}
}

func (r *resolver) setting(kind syn.StatementKind) bool {
	m := r.model
	switch node := kind.(type) {
	case *syn.DateFormat:
		m.DateFormat = node.Token.Value
	case *syn.InclusiveEndDates:
		m.InclusiveEnd = true
	case *syn.TopAxis:
		m.TopAxis = true
	case *syn.AxisFormat:
		m.AxisFormat, m.AxisFormatSpan = node.Token.Value, node.Token.Payload
	case *syn.TickInterval:
		m.TickInterval, m.TickIntervalSpan, m.HasTickInterval = node.Token.Value, node.Token.Payload, true
	default:
		return false
	}
	return true
}

func (r *resolver) calendar(s syn.Statement) bool {
	m := r.model
	switch node := s.Kind.(type) {
	case *syn.Excludes:
		m.Excludes = mergeTokens(m.Excludes, node.Token.Value)
	case *syn.Includes:
		m.Includes = mergeTokens(m.Includes, node.Token.Value)
	case *syn.TodayMarker:
		m.TodayMarker, m.HasTodayMarker = node.Token.Value, true
		r.report(codeToday, "today marker is ignored", s.Span)
	case *syn.Weekday:
		m.Weekday, m.WeekdaySet = node.Name, true
	case *syn.Weekend:
		m.Weekend = node.Name
	default:
		return false
	}
	return true
}

func (r *resolver) text(kind syn.StatementKind) bool {
	m := r.model
	switch node := kind.(type) {
	case *syn.Title:
		m.Title, m.TitleLabel = node.Token.Value, label(node.Token.Value)
	case *syn.AccTitle:
		m.AccTitle = trim(node.Value.Value)
	case *syn.AccDescr:
		m.AccDescr = description(node.Value.Value)
	case *syn.AccDescrBlock:
		m.AccDescr = description(node.Value.Value)
	default:
		return false
	}
	return true
}

func mergeTokens(existing []string, text string) []string {
	for _, token := range strings.FieldsFunc(asciiLower(text), func(c rune) bool { return c == ',' || syn.IsSpace(c) }) {
		if !slices.Contains(existing, token) {
			existing = append(existing, token)
		}
	}
	return existing
}

func (r *resolver) finishDirectives() {
	m := r.model
	if m.AxisFormat != "" {
		if code := unsupportedAxisCode(m.AxisFormat); code != "" {
			r.report(codeAxisUnsupported, "axis format contains unsupported code "+code+"; using "+DefaultAxisForm, m.AxisFormatSpan)
		}
	}
	if m.HasTickInterval {
		if _, unit, ok := parseTickInterval(m.TickInterval); ok && unit == "millisecond" {
			r.report(codeTickUnsupported, "millisecond tick interval is not supported; using automatic ticks", m.TickIntervalSpan)
		}
	}
}

func unsupportedAxisCode(format string) string {
	_, code := civil.Format(0, format)
	return code
}

func parseTickInterval(text string) (every int64, unit string, ok bool) {
	i := 0
	for i < len(text) && text[i] >= '0' && text[i] <= '9' {
		i++
	}
	if i == 0 || text[0] == '0' || i > 9 {
		return 0, "", false
	}
	for _, name := range [...]string{"millisecond", "second", "minute", "hour", "day", "week", "month"} {
		if text[i:] == name {
			var n int64
			for _, c := range text[:i] {
				n = n*10 + int64(c-'0')
			}
			return n, name, true
		}
	}
	return 0, "", false
}

func (r *resolver) addSection(token syn.Token) {
	m := r.model
	m.Sections = append(m.Sections, Section{Name: token.Value, Label: label(token.Value), Span: token.Payload})
	m.Rows = append(m.Rows, Row{Kind: RowSection, Index: len(m.Sections) - 1})
}

func description(text string) string {
	text = trim(text)
	var out strings.Builder
	for i := 0; i < len(text); {
		c := text[i]
		out.WriteByte(c)
		i++
		if c != '\n' {
			continue
		}
		for i < len(text) {
			r, n := utf8.DecodeRuneInString(text[i:])
			if !syn.IsSpace(r) {
				break
			}
			i += n
		}
	}
	return out.String()
}

func (r *resolver) click(node *syn.ClickStatement, span source.Span) {
	c := Click{IDs: node.Click.Value, Span: span}
	if cb := node.Callback; cb != nil {
		callback := &Callback{Name: trim(cb.Value), Span: cb.Payload}
		if node.Args != nil {
			callback.Args = splitCallbackArgs(node.Args.Value)
		}
		c.Callback = callback
		r.report(codeCallbackIgnored, "callback "+callback.Name+" is ignored", cb.Payload)
	}
	if h := node.Href; h != nil {
		c.Href, c.HrefSpan, c.HasHref = h.Value, h.Payload, true
		url, ok := interaction.SafeURL(h.Value)
		if !ok {
			r.report(codeUnsafeURL, "link URL is not allowed", h.Payload)
		}
		for id := range strings.SplitSeq(c.IDs, ",") {
			if at, found := r.ids[id]; found && ok {
				r.model.Tasks[at].Link, r.model.Tasks[at].HasLink = url, true
			}
		}
	}
	r.model.Clicks = append(r.model.Clicks, c)
}

func splitCallbackArgs(text string) []string {
	odd := make([]bool, len(text)+1)
	for i := len(text) - 1; i >= 0; i-- {
		odd[i] = odd[i+1]
		if text[i] == '"' {
			odd[i] = !odd[i]
		}
	}
	var out []string
	from := 0
	for i := range len(text) {
		if text[i] == ',' && !odd[i+1] {
			out = append(out, unquote(trim(text[from:i])))
			from = i + 1
		}
	}
	return append(out, unquote(trim(text[from:])))
}

func unquote(item string) string {
	if len(item) >= 1 && item[0] == '"' && item[len(item)-1] == '"' {
		if len(item) == 1 {
			return ""
		}
		return item[1 : len(item)-1]
	}
	return item
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
		r.readGantt(block)
	}
}

func (r *resolver) readFrontTitle(root syntax.ConfigValue) {
	for _, entry := range root.Entries {
		if entry.Key == "title" && entry.Value.Kind == syntax.ValueString {
			r.model.Title = entry.Value.Text
			r.model.TitleLabel = label(entry.Value.Text)
		}
	}
}

type intRange struct{ low, high int64 }

var integerKeys = map[string]intRange{
	"barHeight":    {1, 1024},
	"barGap":       {0, 1024},
	"topPadding":   {0, 4096},
	"leftPadding":  {0, 4096},
	"rightPadding": {0, 4096},
}

func (r *resolver) readGantt(block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == configKey })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		r.readField(field)
	}
}

func (r *resolver) readField(field syntax.ConfigEntry) {
	if bounds, ok := integerKeys[field.Key]; ok {
		if n, valid := integerValue(field.Value, bounds); valid {
			r.upsert(field.Key, chartmodel.DumpValue{Kind: chartmodel.DumpInteger, Integer: n})
		}
		return
	}
	if value, ok := textField(field); ok {
		r.upsert(field.Key, value)
	}
}

func textField(field syntax.ConfigEntry) (chartmodel.DumpValue, bool) {
	v := field.Value
	isString := v.Kind == syntax.ValueString
	text := chartmodel.DumpValue{Kind: chartmodel.DumpString, String: v.Text}
	switch field.Key {
	case "topAxis":
		return chartmodel.DumpValue{Kind: chartmodel.DumpBool, Bool: v.Bool}, v.Kind == syntax.ValueBool
	case "axisFormat", "tickInterval":
		return text, isString
	case "weekday":
		return text, isString && slices.Contains(weekdayIDs, v.Text)
	}
	return chartmodel.DumpValue{}, false
}

var weekdayIDs = []string{"monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"}

func integerValue(v syntax.ConfigValue, bounds intRange) (int64, bool) {
	if v.Kind != syntax.ValueInteger {
		return 0, false
	}
	var n int64
	text := v.Text
	for i := range len(text) {
		c := text[i]
		if c < '0' || c > '9' || n > bounds.high {
			return 0, false
		}
		n = n*10 + int64(c-'0')
	}
	return n, n >= bounds.low && n <= bounds.high
}

func (r *resolver) upsert(key string, value chartmodel.DumpValue) {
	cfg := &r.model.Config
	if i := slices.IndexFunc(*cfg, func(e chartmodel.ConfigEntry) bool { return e.Key == key }); i >= 0 {
		(*cfg)[i].Value = value
		return
	}
	*cfg = append(*cfg, chartmodel.ConfigEntry{Key: key, Value: value})
}
