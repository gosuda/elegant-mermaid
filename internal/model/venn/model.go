package venn

import (
	"slices"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/venn"
)

const (
	scale       = 1000
	wholeCap    = 1 << 32
	configKey   = "venn"
	maxCanvasPx = 65536
	minCanvasPx = 4
	maxSets     = 3
	titlePrefix = len("title")

	codeNoSets           = "venn/no-sets"
	codeTooMany          = "venn/too-many-sets"
	codeUnionShort       = "venn/union-requires-multiple-identifiers"
	codeUnknownSet       = "venn/unknown-set-identifier"
	codeTextNoSet        = "venn/text-requires-set"
	defaultSizeNumerator = 10 * scale
)

type ConfigEntry struct {
	Key   string
	Value int64
}

type Subset struct {
	Span    source.Span
	Sets    []string
	Label   string
	Display string
	Size    int64
}

type Text struct {
	Span    source.Span
	Sets    []string
	ID      string
	Label   string
	Display string
}

type StyleEntry struct {
	Key   string
	Value string
}

type Style struct {
	Span    source.Span
	Targets []string
	Entries []StyleEntry
}

type Set struct {
	ID      string
	Display string
	Size    int64
	Span    source.Span
}

type Declaration struct {
	SubsetIndex int
	RejectedIDs []string
	Union       bool
	Span        source.Span
	SizeSpan    source.Span
	HasSize     bool
	NonPositive bool
}

type Model struct {
	Title        string
	TitleSpan    source.Span
	Config       []ConfigEntry
	Subsets      []Subset
	Texts        []Text
	Styles       []Style
	HeaderSpan   source.Span
	Declarations []Declaration
}

func (m *Model) Sets() []Set {
	var out []Set
	for _, s := range m.Subsets {
		if len(s.Sets) != 1 {
			continue
		}
		set := Set{ID: s.Sets[0], Display: s.Display, Size: s.Size, Span: s.Span}
		if i := slices.IndexFunc(out, func(o Set) bool { return o.ID == set.ID }); i >= 0 {
			set.Span = out[i].Span
			out[i] = set
			continue
		}
		out = append(out, set)
	}
	return out
}

func (m *Model) Integer(key string) (int64, bool) {
	for _, e := range m.Config {
		if e.Key == key {
			return e.Value, true
		}
	}
	return 0, false
}

type resolver struct {
	model      *Model
	known      map[string]struct{}
	current    []string
	hasCurrent bool
	diags      []diag.Diagnostic
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{}, known: map[string]struct{}{}}
	r.model.HeaderSpan = document.Header.Span
	r.readConfig(syntax.Preprocess(src))
	for _, line := range document.Document.Lines {
		if line.Statement != nil {
			r.statement(line.Statement.Kind)
		}
	}
	r.checkSetCount(document.Header.Span)
	slices.SortFunc(r.model.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	return r.model, r.diags
}

func (r *resolver) issue(code, message string, span source.Span, related ...source.Span) {
	d := syn.Diagnostic(code, message, span)
	for _, s := range related {
		d.Related = append(d.Related, diag.Related{Span: s, Message: "also unknown"})
	}
	r.diags = append(r.diags, d)
}

func (r *resolver) checkSetCount(header source.Span) {
	sets := r.model.Sets()
	switch {
	case len(sets) == 0:
		r.issue(codeNoSets, "venn diagram has no sets", header)
	case len(sets) > maxSets:
		r.issue(codeTooMany, "venn diagram has more than three sets", sets[maxSets].Span)
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
		r.readVenn(block)
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

func (r *resolver) readVenn(block syntax.ConfigValue) {
	venn, ok := mapping(block, configKey)
	if !ok {
		return
	}
	for _, field := range venn.Entries {
		if field.Key != "width" && field.Key != "height" || field.Value.Kind != syntax.ValueInteger {
			continue
		}
		n, err := strconv.ParseInt(field.Value.Text, 10, 64)
		if err == nil && n >= minCanvasPx && n <= maxCanvasPx {
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

func normalize(text string) string {
	trimmed := strings.TrimFunc(text, jsSpace)
	if len(trimmed) >= 2 && strings.HasPrefix(trimmed, "\"") && strings.HasSuffix(trimmed, "\"") {
		return trimmed[1 : len(trimmed)-1]
	}
	return trimmed
}

func normalizeList(list syn.IdentifierList) []string {
	out := make([]string, len(list.IDs))
	for i, id := range list.IDs {
		out[i] = normalize(id.Text)
	}
	return out
}

func sorted(ids []string) []string {
	out := slices.Clone(ids)
	slices.Sort(out)
	return out
}

func optionalLabel(token *syn.Token) string {
	if token == nil || token.Text == "" {
		return ""
	}
	return normalize(token.Text)
}

func (r *resolver) statement(kind syn.StatementKind) {
	switch s := kind.(type) {
	case *syn.Title:
		_, size := utf8.DecodeRuneInString(s.Token.Text[titlePrefix:])
		r.model.Title, r.model.TitleSpan = strings.TrimSpace(syntax.DecodeEntities(s.Token.Text[titlePrefix+size:])), s.Span
	case *syn.Set:
		r.declaration(false, s.ID.Span, s.Size)
		r.subset(s.Span, syn.IdentifierList{IDs: []syn.Identifier{s.ID}}, s.Label, s.Size)
	case *syn.Union:
		r.union(s)
	case *syn.Text:
		r.addText(s.Span, sorted(normalizeList(s.Targets)), s.ID, s.Label)
	case *syn.IndentedText:
		r.indentedText(s)
	case *syn.Style:
		r.addStyle(s)
	}
}

func (r *resolver) union(s *syn.Union) {
	r.declaration(true, s.IDs.Span, s.Size)
	if len(s.IDs.IDs) < 2 {
		r.model.Declarations[len(r.model.Declarations)-1].RejectedIDs = sorted(normalizeList(s.IDs))
		r.issue(codeUnionShort, "union requires multiple identifiers", s.IDs.Span)
		return
	}
	var unknown []syn.Identifier
	var names []string
	for i, name := range normalizeList(s.IDs) {
		if _, ok := r.known[name]; !ok {
			unknown = append(unknown, s.IDs.IDs[i])
			names = append(names, name)
		}
	}
	if len(unknown) > 0 {
		r.model.Declarations[len(r.model.Declarations)-1].RejectedIDs = sorted(normalizeList(s.IDs))
		var rest []source.Span
		for _, id := range unknown[1:] {
			rest = append(rest, id.Span)
		}
		r.issue(codeUnknownSet, "unknown set identifier: "+strings.Join(names, ", "), unknown[0].Span, rest...)
		return
	}
	r.subset(s.Span, s.IDs, s.Label, s.Size)
}

func (r *resolver) declaration(union bool, span source.Span, size *syn.Number) {
	d := Declaration{SubsetIndex: -1, Union: union, Span: span}
	if size != nil {
		d.HasSize, d.SizeSpan = true, size.Span
		d.NonPositive = strings.HasPrefix(size.Text, "-") || !strings.ContainsAny(size.Text, "123456789")
	}
	r.model.Declarations = append(r.model.Declarations, d)
}

func (r *resolver) subset(span source.Span, ids syn.IdentifierList, label *syn.Token, size *syn.Number) {
	sets := sorted(normalizeList(ids))
	subset := Subset{Span: span, Sets: sets, Size: defaultSize(len(ids.IDs))}
	if size != nil {
		subset.Size = Thousandths(size.Text)
	}
	if subset.Label = optionalLabel(label); subset.Label != "" {
		subset.Display = syntax.DecodeEntities(subset.Label)
	}
	if len(sets) == 1 {
		r.known[sets[0]] = struct{}{}
		if subset.Display == "" {
			subset.Display = syntax.DecodeEntities(sets[0])
		}
	}
	r.current, r.hasCurrent = sets, true
	d := &r.model.Declarations[len(r.model.Declarations)-1]
	d.SubsetIndex, d.RejectedIDs = len(r.model.Subsets), nil
	r.model.Subsets = append(r.model.Subsets, subset)
}

func defaultSize(count int) int64 {
	square := int64(count) * int64(count)
	return (2*defaultSizeNumerator + square) / (2 * square)
}

func (r *resolver) indentedText(s *syn.IndentedText) {
	if !r.hasCurrent {
		r.issue(codeTextNoSet, "text requires set", s.Span)
		return
	}
	r.addText(s.Span, r.current, s.Tail.ID, s.Tail.Label)
}

func (r *resolver) addText(span source.Span, sets []string, id syn.Identifier, label *syn.Token) {
	text := Text{Span: span, Sets: sets, ID: normalize(id.Text), Label: optionalLabel(label)}
	text.Display = syntax.DecodeEntities(text.ID)
	if text.Label != "" {
		text.Display = syntax.DecodeEntities(text.Label)
	}
	r.model.Texts = append(r.model.Texts, text)
}

func (r *resolver) addStyle(s *syn.Style) {
	style := Style{Span: s.Span, Targets: sorted(normalizeList(s.Targets))}
	for _, field := range s.Styles.Fields {
		entry := StyleEntry{Key: field.Key.Text, Value: styleValue(field.Value)}
		if i := slices.IndexFunc(style.Entries, func(e StyleEntry) bool { return e.Key == entry.Key }); i >= 0 {
			style.Entries[i].Value = entry.Value
			continue
		}
		style.Entries = append(style.Entries, entry)
	}
	r.model.Styles = append(r.model.Styles, style)
}

func styleValue(v syn.StyleValue) string {
	if v.String != nil {
		return normalize(v.String.Text)
	}
	parts := make([]string, len(v.Tokens.Tokens))
	for i, t := range v.Tokens.Tokens {
		parts[i] = t.Text
	}
	return normalize(strings.Join(parts, " "))
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
