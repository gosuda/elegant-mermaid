package cynefin

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/cynefin"
	"github.com/gosuda/elegant-mermaid/internal/syntax/langium"
)

const (
	configKey   = "cynefin"
	maxCanvasPx = 65536
	maxSeed     = 1<<32 - 1
	selfLoop    = "cynefin/self-loop-transition"
)

type Item struct {
	Label string
	Span  source.Span
}

type Domain struct {
	Name     string
	Declared bool
	Span     source.Span
	Items    []Item
}

type Transition struct {
	From  string
	To    string
	Label string
	Span  source.Span
}

type ConfigEntry struct {
	Key   string
	Value int64
}

type Model struct {
	Title       string
	TitleSpan   source.Span
	AccTitle    string
	AccDescr    string
	Domains     []Domain
	Transitions []Transition
	Config      []ConfigEntry
}

type intRange struct{ low, high int64 }

var integerKeys = map[string]intRange{
	"width":             {1, maxCanvasPx},
	"height":            {1, maxCanvasPx},
	"boundaryAmplitude": {0, maxCanvasPx},
	"seed":              {1, maxSeed},
}

func Resolve(src []byte, ast *syn.Cynefin) (*Model, []diag.Diagnostic) {
	m := &Model{}
	m.readConfig(syntax.Preprocess(src))
	m.domains(ast.Domains)
	diagnostics := m.transitions(ast.Transitions)
	m.metadata(ast)
	slices.SortFunc(m.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return m, diagnostics
}

func (m *Model) domains(blocks []syn.DomainBlock) {
	for _, block := range blocks {
		domain := Domain{Name: block.Domain.Text, Declared: true, Span: block.Span}
		for _, item := range block.Items {
			domain.Items = append(domain.Items, Item{Label: syntax.DecodeEntities(item.Label.Text), Span: item.Span})
		}
		if i := slices.IndexFunc(m.Domains, func(d Domain) bool { return d.Name == domain.Name }); i >= 0 {
			m.Domains[i] = domain
			continue
		}
		m.Domains = append(m.Domains, domain)
	}
	for _, name := range syn.DomainNames {
		if !slices.ContainsFunc(m.Domains, func(d Domain) bool { return d.Name == name }) {
			m.Domains = append(m.Domains, Domain{Name: name})
		}
	}
}

func (m *Model) transitions(nodes []syn.Transition) []diag.Diagnostic {
	var out []diag.Diagnostic
	for _, node := range nodes {
		if node.From.Text == node.To.Text {
			out = append(out, selfLoopWarning(node))
			continue
		}
		t := Transition{From: node.From.Text, To: node.To.Text, Span: node.Span}
		if node.Label != nil {
			t.Label = syntax.DecodeEntities(node.Label.Text)
		}
		m.Transitions = append(m.Transitions, t)
	}
	return out
}

func selfLoopWarning(node syn.Transition) diag.Diagnostic {
	return langium.Diagnostic(selfLoop, diag.SeverityWarning, "self-loop transition on domain "+node.From.Text+" is skipped", node.Span)
}

func (m *Model) metadata(ast *syn.Cynefin) {
	if ast.Title != nil {
		m.Title, m.TitleSpan = strings.TrimSpace(syntax.DecodeEntities(ast.Title.Text)), ast.Title.Span
	}
	if ast.AccTitle != nil {
		m.AccTitle = ast.AccTitle.Text
	}
	if ast.AccDescr != nil {
		m.AccDescr = ast.AccDescr.Text
	}
}

func (m *Model) readConfig(pre syntax.Preprocessed) {
	if pre.HasFront {
		m.readFrontTitle(pre.Root)
	}
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		m.readChart(block)
	}
}

func (m *Model) readFrontTitle(root syntax.ConfigValue) {
	for _, entry := range root.Entries {
		if entry.Key == "title" && entry.Value.Kind == syntax.ValueString {
			m.Title = strings.TrimSpace(syntax.DecodeEntities(entry.Value.Text))
		}
	}
}

func (m *Model) readChart(block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == configKey })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		bounds, known := integerKeys[field.Key]
		if !known {
			continue
		}
		if n, ok := integer(field.Value, bounds); ok {
			m.upsert(field.Key, n)
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

func (m *Model) upsert(key string, value int64) {
	if i := slices.IndexFunc(m.Config, func(e ConfigEntry) bool { return e.Key == key }); i >= 0 {
		m.Config[i].Value = value
		return
	}
	m.Config = append(m.Config, ConfigEntry{Key: key, Value: value})
}
