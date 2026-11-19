package sankey

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/sankey"
)

const (
	configKey   = "sankey"
	maxCanvasPx = 65536
)

var alignments = []string{"left", "right", "center", "justify"}

type DumpKind uint8

const (
	DumpBool DumpKind = iota
	DumpInteger
	DumpString
)

type DumpValue struct {
	Kind    DumpKind
	Bool    bool
	Integer int64
	String  string
}

type ConfigEntry struct {
	Key   string
	Value DumpValue
}

type Node struct {
	ID   string
	Span source.Span
}

type Link struct {
	Source int
	Target int
	Value  Value
	Span   source.Span
}

type Model struct {
	Config []ConfigEntry
	Nodes  []Node
	Links  []Link
}

type resolver struct {
	model *Model
	index map[string]int
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{}, index: map[string]int{}}
	r.readConfig(syntax.Preprocess(src))
	for _, record := range document.Csv.Records {
		r.record(record)
	}
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, nil
}

func (r *resolver) record(record syn.Record) {
	from := r.node(record.Source)
	to := r.node(record.Target)
	r.model.Links = append(r.model.Links, Link{Source: from, Target: to, Value: ParseValue(record.Value.Text()), Span: record.Span})
}

func (r *resolver) node(field syn.Field) int {
	id := syntax.DecodeEntities(strings.ReplaceAll(strings.TrimSpace(field.Text()), `""`, `"`))
	if at, found := r.index[id]; found {
		return at
	}
	at := len(r.model.Nodes)
	r.index[id] = at
	r.model.Nodes = append(r.model.Nodes, Node{ID: id, Span: field.Span})
	return at
}

func (r *resolver) readConfig(pre syntax.Preprocessed) {
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		r.readSankey(block)
	}
}

func (r *resolver) readSankey(block syntax.ConfigValue) {
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
	switch field.Key {
	case "width", "height":
		if n, ok := pixels(field.Value); ok {
			r.upsert(field.Key, DumpValue{Kind: DumpInteger, Integer: n})
		}
	case "showValues":
		if field.Value.Kind == syntax.ValueBool {
			r.upsert(field.Key, DumpValue{Kind: DumpBool, Bool: field.Value.Bool})
		}
	case "nodeAlignment":
		if field.Value.Kind == syntax.ValueString && slices.Contains(alignments, field.Value.Text) {
			r.upsert(field.Key, DumpValue{Kind: DumpString, String: field.Value.Text})
		}
	}
}

func pixels(value syntax.ConfigValue) (int64, bool) {
	if value.Kind != syntax.ValueInteger {
		return 0, false
	}
	n, err := strconv.ParseInt(value.Text, 10, 64)
	return n, err == nil && n >= 1 && n <= maxCanvasPx
}

func (r *resolver) upsert(key string, value DumpValue) {
	if i := slices.IndexFunc(r.model.Config, func(e ConfigEntry) bool { return e.Key == key }); i >= 0 {
		r.model.Config[i].Value = value
		return
	}
	r.model.Config = append(r.model.Config, ConfigEntry{Key: key, Value: value})
}
