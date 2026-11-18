package gitgraph

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gitgraph"
)

const DefaultMainBranch = "main"

var honoured = []string{"rotateCommitLabel", "showBranches", "showCommitLabel"}

type CommitKind uint8

const (
	KindCommit CommitKind = iota
	KindMerge
	KindCherryPick
)

type CommitType uint8

const (
	TypeNormal CommitType = iota
	TypeReverse
	TypeHighlight
)

type Branch struct {
	Name     string
	Order    int64
	HasOrder bool
	Span     source.Span
}

type Commit struct {
	ID      string
	Seq     int
	Branch  int
	Parents []string
	Pick    string
	Kind    CommitKind
	Type    CommitType
	Tags    []string
	Message string
	Span    source.Span
}

type ConfigEntry struct {
	Key   string
	Value bool
}

type Model struct {
	AccTitle      string
	AccDescr      string
	Title         string
	Direction     string
	Branches      []Branch
	Commits       []Commit
	Config        []ConfigEntry
	CommitHistory []Commit
}

type head struct {
	id  string
	set bool
}

type resolver struct {
	model   *Model
	diags   []diag.Diagnostic
	heads   []head
	current int
	seq     int
	commits map[string]int
	names   map[string]int
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := newResolver(src, document)
	for _, statement := range document.Statements {
		r.statement(statement)
	}
	return r.model, r.diags
}

func newResolver(src []byte, document *syn.Start) *resolver {
	model := &Model{Direction: "LR", Branches: []Branch{{Name: DefaultMainBranch}}}
	if document.Direction != nil {
		model.Direction = document.Direction.Kind
	}
	pre := syntax.Preprocess(src)
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		readConfig(model, block)
	}
	slices.SortFunc(model.Config, func(a, b ConfigEntry) int { return compareKeys(a.Key, b.Key) })
	return &resolver{model: model, heads: []head{{}}, commits: map[string]int{}, names: map[string]int{model.Branches[0].Name: 0}}
}

func compareKeys(a, b string) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func readConfig(model *Model, block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == "gitGraph" })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		readField(model, field)
	}
}

func readField(model *Model, field syntax.ConfigEntry) {
	switch {
	case field.Key == "mainBranchName":
		readMainName(model, field.Value)
	case field.Key == "mainBranchOrder":
		readMainOrder(model, field.Value)
	case field.Value.Kind == syntax.ValueBool && slices.Contains(honoured, field.Key):
		model.Config = upsert(model.Config, ConfigEntry{Key: field.Key, Value: field.Value.Bool})
	}
}

func readMainName(model *Model, value syntax.ConfigValue) {
	if value.Kind == syntax.ValueString && value.Text != "" {
		model.Branches[0].Name = value.Text
	}
}

func readMainOrder(model *Model, value syntax.ConfigValue) {
	if value.Kind != syntax.ValueInteger {
		return
	}
	if order, err := strconv.ParseInt(value.Text, 10, 64); err == nil {
		model.Branches[0].Order, model.Branches[0].HasOrder = order, true
	}
}

func upsert(entries []ConfigEntry, entry ConfigEntry) []ConfigEntry {
	if i := slices.IndexFunc(entries, func(e ConfigEntry) bool { return e.Key == entry.Key }); i >= 0 {
		entries[i] = entry
		return entries
	}
	return append(entries, entry)
}

func (r *resolver) issue(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func (r *resolver) statement(statement syn.Statement) {
	switch node := statement.Kind.(type) {
	case *syn.Commit:
		r.commit(statement.Span, node)
	case *syn.Branch:
		r.branch(node)
	case *syn.Merge:
		r.merge(statement.Span, node)
	case *syn.Checkout:
		r.checkout(node)
	case *syn.CherryPicking:
		r.cherryPick(statement.Span, node)
	case *syn.Metadata:
		r.metadata(node)
	}
}

func (r *resolver) metadata(node *syn.Metadata) {
	switch node.Field {
	case "title":
		r.model.Title = node.Value
	case "accTitle":
		r.model.AccTitle = node.Value
	default:
		r.model.AccDescr = node.Value
	}
}

func commitType(value *syn.Value) CommitType {
	if value == nil {
		return TypeNormal
	}
	switch value.Text {
	case "REVERSE":
		return TypeReverse
	case "HIGHLIGHT":
		return TypeHighlight
	}
	return TypeNormal
}

func values(tags []syn.Value) []string {
	out := make([]string, len(tags))
	for i, tag := range tags {
		out[i] = tag.Text
	}
	return out
}
