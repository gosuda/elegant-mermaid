package pie

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/pie"
)

const (
	configKey       = "pie"
	DonutHoleKey    = "donutHole"
	TextPositionKey = "textPosition"
	DonutHoleMax    = 900
	TextPositionMax = 1000
	Overflow        = int64(1) << 32
	scale           = 1000
)

type Section struct {
	Label string
	Value int64
	Index int
	Span  source.Span
}

type ConfigEntry struct {
	Key   string
	Value int64
}

type SectionOccurrence struct {
	Section    int
	Label      string
	LabelSpan  source.Span
	NumberSpan source.Span
	ExactZero  bool
}

type Model struct {
	AccTitle    string
	AccDescr    string
	Title       string
	ShowData    bool
	Sections    []Section
	Config      []ConfigEntry
	Header      source.Span
	Occurrences []SectionOccurrence
}

func Resolve(src []byte, document *syn.Pie) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{ShowData: document.ShowData, Header: document.Header.Span}, last: map[string]string{}}
	r.readConfig(syntax.Preprocess(src))
	for _, statement := range document.Body {
		switch node := statement.Kind.(type) {
		case *syn.PieSection:
			r.section(node)
		case *syn.TitleAndAccessibilities:
			for _, item := range node.Items {
				r.last[item.Field] = item.Value
			}
		}
	}
	r.applyMetadata()
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, r.diags
}

type resolver struct {
	model *Model
	diags []diag.Diagnostic
	seen  int
	last  map[string]string
}

func (r *resolver) applyMetadata() {
	if title := strings.TrimSpace(syntax.DecodeEntities(r.last["title"])); title != "" {
		r.model.Title = title
	}
	if value := r.last["accTitle"]; value != "" {
		r.model.AccTitle = value
	}
	if value := r.last["accDescr"]; value != "" {
		r.model.AccDescr = value
	}
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
		r.readPie(block)
	}
}

func (r *resolver) readFrontTitle(root syntax.ConfigValue) {
	for _, entry := range root.Entries {
		if entry.Key == "title" && entry.Value.Kind == syntax.ValueString {
			r.model.Title = strings.TrimSpace(syntax.DecodeEntities(entry.Value.Text))
		}
	}
}

func (r *resolver) readPie(block syntax.ConfigValue) {
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
	limit := int64(0)
	switch field.Key {
	case DonutHoleKey:
		limit = DonutHoleMax
	case TextPositionKey:
		limit = TextPositionMax
	default:
		return
	}
	if field.Value.Kind != syntax.ValueInteger && field.Value.Kind != syntax.ValueDecimal {
		return
	}
	if n, negative := Thousandths(field.Value.Text); !negative && n <= limit {
		r.upsert(field.Key, n)
	}
}

func (r *resolver) upsert(key string, value int64) {
	if i := slices.IndexFunc(r.model.Config, func(e ConfigEntry) bool { return e.Key == key }); i >= 0 {
		r.model.Config[i].Value = value
		return
	}
	r.model.Config = append(r.model.Config, ConfigEntry{Key: key, Value: value})
}

func (r *resolver) section(node *syn.PieSection) {
	index := r.seen
	r.seen++
	label := syntax.DecodeEntities(node.Label.Text)
	value, negative := Thousandths(node.Number.Text)
	occurrence := SectionOccurrence{
		Section: -1, Label: label, LabelSpan: node.Label.Span,
		NumberSpan: node.Number.Span, ExactZero: strings.Trim(node.Number.Text, "+-0.") == "",
	}
	if !negative {
		occurrence.Section = slices.IndexFunc(r.model.Sections, func(s Section) bool { return s.Label == label })
		if occurrence.Section < 0 {
			occurrence.Section = len(r.model.Sections)
		}
		occurrence.Label = ""
	}
	r.model.Occurrences = append(r.model.Occurrences, occurrence)
	if negative {
		r.diags = append(r.diags, syn.Diagnostic("pie/negative-value", "slice "+label+" has negative value "+node.Number.Text, node.Number.Span))
		return
	}
	if occurrence.Section < len(r.model.Sections) {
		return
	}
	r.model.Sections = append(r.model.Sections, Section{Label: label, Value: value, Index: index, Span: node.Number.Span})
}

func Thousandths(literal string) (magnitude int64, negative bool) {
	whole, fraction, _ := strings.Cut(strings.TrimLeft(literal, "+-"), ".")
	var units int64
	for i := range len(whole) {
		units = min(units*10+int64(whole[i]-'0'), Overflow)
	}
	magnitude = units * scale
	var tail int64
	for i := range 4 {
		tail *= 10
		if i < len(fraction) {
			tail += int64(fraction[i] - '0')
		}
	}
	magnitude += tail / 10
	if tail%10 >= 5 {
		magnitude++
	}
	negative = strings.HasPrefix(literal, "-") && strings.Trim(literal, "-0.") != ""
	return min(magnitude, Overflow), negative
}
