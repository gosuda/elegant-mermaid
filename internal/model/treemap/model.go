package treemap

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/treemap"
)

const (
	scale       = 1000
	wholeCap    = 1 << 32
	maxDepth    = 64
	configKey   = "treemap"
	maxCanvasPx = 65536
)

type ConfigEntry struct {
	Key   string
	Value int64
}

type Class struct {
	Name       string
	Styles     []string
	TextStyles []string
}

type Node struct {
	Name             string
	Leaf             bool
	Value            int64
	Selector         string
	Styles           []string
	Index            int
	Span             source.Span
	NameSpan         source.Span
	ValueSpan        source.Span
	ExactZero        bool
	NextMoreIndented bool
	ParentIndex      int
	Children         []*Node
}

type Model struct {
	AccTitle string
	AccDescr string
	Title    string
	Config   []ConfigEntry
	Classes  []Class
	Roots    []*Node
	Count    int
	Span     source.Span
	Nodes    []*Node
}

type intRange struct{ low, high int64 }

var integerKeys = map[string]intRange{
	"padding":    {0, maxCanvasPx},
	"nodeWidth":  {1, maxCanvasPx},
	"nodeHeight": {1, maxCanvasPx},
}

func Resolve(src []byte, document *syn.Treemap) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{Span: document.Span}}
	r.readConfig(syntax.Preprocess(src))
	r.metadata(document)
	r.collectClasses(document)
	r.build(document)
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, r.diags
}

type resolver struct {
	model *Model
	diags []diag.Diagnostic
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
		r.readTreemap(block)
	}
}

func (r *resolver) readFrontTitle(root syntax.ConfigValue) {
	for _, entry := range root.Entries {
		if entry.Key == "title" && entry.Value.Kind == syntax.ValueString {
			r.model.Title = strings.TrimSpace(entry.Value.Text)
		}
	}
}

func (r *resolver) readTreemap(block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == configKey })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		bounds, known := integerKeys[field.Key]
		if !known || field.Value.Kind != syntax.ValueInteger {
			continue
		}
		if n, err := strconv.ParseInt(field.Value.Text, 10, 64); err == nil && n >= bounds.low && n <= bounds.high {
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

func (r *resolver) metadata(document *syn.Treemap) {
	last := map[string]string{}
	for _, row := range document.Rows {
		group, ok := row.(*syn.TitleAndAccessibilities)
		if !ok {
			continue
		}
		for _, token := range group.Tokens {
			last[token.Kind] = token.Text
		}
	}
	if title := last["TITLE"]; title != "" {
		r.model.Title = title
	}
	r.model.AccTitle = last["ACC_TITLE"]
	r.model.AccDescr = last["ACC_DESCR"]
}

var labelStyles = []string{
	"color", "font-size", "font-family", "font-weight", "font-style", "text-decoration", "text-align",
	"text-transform", "line-height", "letter-spacing", "word-spacing", "text-shadow", "text-overflow",
	"white-space", "word-wrap", "word-break", "overflow-wrap", "hyphens",
}

const commaSentinel = "\x00"

func splitStyles(text string) []string {
	text = strings.ReplaceAll(text, "\\,", commaSentinel)
	text = strings.ReplaceAll(text, ",", ";")
	text = strings.ReplaceAll(text, commaSentinel, ",")
	return strings.Split(text, ";")
}

func (r *resolver) collectClasses(document *syn.Treemap) {
	for _, row := range document.Rows {
		entry, ok := row.(*syn.TreemapRow)
		if !ok || entry.ClassDef == nil {
			continue
		}
		r.addClass(entry.ClassDef.Name, entry.ClassDef.Style)
	}
}

func (r *resolver) addClass(name, style string) {
	i := slices.IndexFunc(r.model.Classes, func(c Class) bool { return c.Name == name })
	if i < 0 {
		r.model.Classes = append(r.model.Classes, Class{Name: name})
		i = len(r.model.Classes) - 1
	}
	class := &r.model.Classes[i]
	for _, s := range splitStyles(style) {
		if slices.Contains(labelStyles, s) {
			class.TextStyles = append(class.TextStyles, s)
		}
		class.Styles = append(class.Styles, s)
	}
}

func (r *resolver) stylesOf(selector string) []string {
	for _, c := range r.model.Classes {
		if c.Name == selector {
			return slices.Clone(c.Styles)
		}
	}
	return nil
}

type frame struct {
	node  *Node
	level int
}

func rowLevel(entry *syn.TreemapRow) int {
	if entry.Indent == nil {
		return 0
	}
	return entry.Indent.Width
}

func (r *resolver) attach(stack []frame, node *Node, level int) []frame {
	for len(stack) > 0 && stack[len(stack)-1].level >= level {
		stack = stack[:len(stack)-1]
	}
	node.ParentIndex = -1
	if len(stack) == 0 {
		r.model.Roots = append(r.model.Roots, node)
	} else {
		parent := stack[len(stack)-1].node
		node.ParentIndex = parent.Index
		parent.Children = append(parent.Children, node)
	}
	if !node.Leaf {
		stack = append(stack, frame{node: node, level: level})
	}
	return stack
}

func (r *resolver) build(document *syn.Treemap) {
	var stack []frame
	deep := false
	var previous *Node
	previousLevel := 0
	for _, row := range document.Rows {
		entry, ok := row.(*syn.TreemapRow)
		if !ok || entry.Item == nil {
			continue
		}
		level := rowLevel(entry)
		if previous != nil && previous.Leaf {
			previous.NextMoreIndented = level > previousLevel
		}
		node := r.node(entry.Item)
		stack = r.attach(stack, node, level)
		r.model.Nodes = append(r.model.Nodes, node)
		previous, previousLevel = node, level
		if len(stack) > maxDepth && !deep {
			deep = true
			r.diags = append(r.diags, syn.Diagnostic("limit/nesting-depth", "nesting depth exceeds 64", node.Span))
		}
	}
}

func (r *resolver) node(item syn.Item) *Node {
	index := r.model.Count
	r.model.Count++
	switch v := item.(type) {
	case *syn.Leaf:
		node := &Node{Name: v.Name.Value, Leaf: true, Index: index, Span: v.Span, NameSpan: v.Name.Span, ValueSpan: v.Value.Span}
		if v.Value.Valid {
			node.Value = Thousandths(v.Value.Literal)
			node.ExactZero = strings.Trim(v.Value.Literal, "0.") == ""
		}
		r.selector(node, v.ClassSelector)
		return node
	case *syn.Section:
		node := &Node{Name: v.Name.Value, Index: index, Span: v.Span, NameSpan: v.Name.Span}
		r.selector(node, v.ClassSelector)
		return node
	}
	return &Node{Index: index}
}

func (r *resolver) selector(node *Node, selector *syn.ClassSelector) {
	if selector == nil {
		return
	}
	node.Selector = selector.Name
	node.Styles = r.stylesOf(selector.Name)
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

func FormatValue(thousandths int64) string {
	whole := strconv.FormatInt(thousandths/scale, 10)
	var grouped strings.Builder
	for i := range len(whole) {
		if i > 0 && (len(whole)-i)%3 == 0 {
			grouped.WriteByte(',')
		}
		grouped.WriteByte(whole[i])
	}
	fraction := thousandths % scale
	if fraction == 0 {
		return grouped.String()
	}
	digits := strings.TrimRight(strconv.FormatInt(scale+fraction, 10)[1:], "0")
	return grouped.String() + "." + digits
}
