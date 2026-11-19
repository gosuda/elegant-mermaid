package packet

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/packet"
)

const (
	codeRangeReversed = "packet/range-reversed"
	codeNonContiguous = "packet/non-contiguous"
	codeZeroBitField  = "packet/zero-bit-field"

	DefaultBitsPerRow = 32
	MaxWords          = 10000
	ConfigMax         = 1024
)

type ConfigKind uint8

const (
	ConfigInteger ConfigKind = iota
	ConfigBool
	ConfigString
)

type ConfigEntry struct {
	Key  string
	Kind ConfigKind
	Int  int64
	Bool bool
	Text string
}

type Field struct {
	Index                     int
	Start, End, Bits          int64
	Label                     string
	Span                      source.Span
	StartSpan, EndSpan        source.Span
	BitsSpan, LabelSpan       source.Span
	HasStart, HasEnd, HasBits bool
}

type Piece struct {
	Field            int
	Row              int
	Start, End, Bits int64
	Label            string
}

type Model struct {
	AccTitle   string
	AccDescr   string
	Title      string
	Fields     []Field
	Pieces     []Piece
	Rows       int
	BitsPerRow int64
	ShowBits   bool
	Descending bool
	Config     []ConfigEntry
}

type setting struct {
	key      string
	kind     ConfigKind
	min, max int64
}

var settings = []setting{
	{"bitOrder", ConfigString, 0, 0},
	{"bitWidth", ConfigInteger, 1, ConfigMax},
	{"bitsPerRow", ConfigInteger, 1, ConfigMax},
	{"paddingX", ConfigInteger, 0, ConfigMax},
	{"paddingY", ConfigInteger, 0, ConfigMax},
	{"rowHeight", ConfigInteger, 1, ConfigMax},
	{"showBits", ConfigBool, 0, 0},
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	m := &Model{BitsPerRow: DefaultBitsPerRow, ShowBits: true}
	pre := syntax.Preprocess(src)
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		readConfig(m, block)
	}
	slices.SortFunc(m.Config, func(a, b ConfigEntry) int { return strings.Compare(a.Key, b.Key) })
	m.applyConfig()
	r := &resolver{model: m, last: -1}
	for _, statement := range document.Statements {
		r.statement(statement)
	}
	if r.diags == nil {
		m.split()
	}
	return m, r.diags
}

func readConfig(m *Model, block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == "packet" })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		if entry, ok := configEntry(field); ok {
			m.upsert(entry)
		}
	}
}

func configEntry(field syntax.ConfigEntry) (ConfigEntry, bool) {
	i := slices.IndexFunc(settings, func(s setting) bool { return s.key == field.Key })
	if i < 0 {
		return ConfigEntry{}, false
	}
	switch s := settings[i]; s.kind {
	case ConfigBool:
		return boolEntry(s, field.Value)
	case ConfigString:
		return stringEntry(s, field.Value)
	default:
		return integerEntry(s, field.Value)
	}
}

func boolEntry(s setting, value syntax.ConfigValue) (ConfigEntry, bool) {
	return ConfigEntry{Key: s.key, Kind: ConfigBool, Bool: value.Bool}, value.Kind == syntax.ValueBool
}

func stringEntry(s setting, value syntax.ConfigValue) (ConfigEntry, bool) {
	ordered := value.Text == "ascending" || value.Text == "descending"
	return ConfigEntry{Key: s.key, Kind: ConfigString, Text: value.Text}, value.Kind == syntax.ValueString && ordered
}

func integerEntry(s setting, value syntax.ConfigValue) (ConfigEntry, bool) {
	if value.Kind != syntax.ValueInteger {
		return ConfigEntry{}, false
	}
	n, err := strconv.ParseInt(value.Text, 10, 64)
	return ConfigEntry{Key: s.key, Kind: ConfigInteger, Int: n}, err == nil && n >= s.min && n <= s.max
}

func (m *Model) upsert(entry ConfigEntry) {
	if i := slices.IndexFunc(m.Config, func(e ConfigEntry) bool { return e.Key == entry.Key }); i >= 0 {
		m.Config[i] = entry
		return
	}
	m.Config = append(m.Config, entry)
}

func (m *Model) applyConfig() {
	for _, entry := range m.Config {
		switch entry.Key {
		case "bitsPerRow":
			m.BitsPerRow = entry.Int
		case "showBits":
			m.ShowBits = entry.Bool
		case "bitOrder":
			m.Descending = entry.Text == "descending"
		}
	}
}

type resolver struct {
	model *Model
	diags []diag.Diagnostic
	last  int64
}

func (r *resolver) statement(statement syn.Statement) {
	if len(r.diags) > 0 {
		return
	}
	switch node := statement.Kind.(type) {
	case *syn.Metadata:
		r.metadata(node)
	case *syn.PacketBlock:
		r.block(statement.Span, node)
	}
}

func (r *resolver) metadata(node *syn.Metadata) {
	switch node.Field {
	case "title":
		r.model.Title = node.Value
	case "accTitle":
		r.model.AccTitle = node.Value
	case "accDescr":
		r.model.AccDescr = node.Value
	}
}

func (r *resolver) issue(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func (r *resolver) block(span source.Span, node *syn.PacketBlock) {
	f := newField(len(r.model.Fields), span, node)
	if code, message, at := r.check(f); code != "" {
		r.issue(code, message, at)
		return
	}
	r.complete(&f)
	r.last = f.End
	r.model.Fields = append(r.model.Fields, f)
}

func newField(index int, span source.Span, node *syn.PacketBlock) Field {
	f := Field{Index: index, Label: node.Label.Text, Span: span, LabelSpan: node.Label.Span}
	if o := node.Start; o != nil {
		f.Start, f.StartSpan, f.HasStart = o.Value, o.Span, true
	}
	if o := node.End; o != nil {
		f.End, f.EndSpan, f.HasEnd = o.Value, o.Span, true
	}
	if o := node.Bits; o != nil {
		f.Bits, f.BitsSpan, f.HasBits = o.Value, o.Span, true
	}
	return f
}

func (r *resolver) check(f Field) (code, message string, at source.Span) {
	if f.HasStart && f.HasEnd && f.End < f.Start {
		return codeRangeReversed, "Packet block " + number(f.Start) + " - " + number(f.End) + " is invalid. End must be greater than start.", source.Span{Start: f.StartSpan.Start, End: f.EndSpan.End}
	}
	start, shown := r.last+1, r.last+1
	if f.HasStart {
		start, shown = f.Start, f.Start
	}
	if f.HasEnd {
		shown = f.End
	}
	if start != r.last+1 {
		return codeNonContiguous, "Packet block " + number(start) + " - " + number(shown) + " is not contiguous. It should start from " + number(r.last+1) + ".", f.StartSpan
	}
	if f.HasBits && f.Bits == 0 {
		return codeZeroBitField, "Packet block " + number(start) + " is invalid. Cannot have a zero bit field.", f.BitsSpan
	}
	return "", "", source.Span{}
}

func number(value int64) string { return strconv.FormatInt(value, 10) }

func (r *resolver) complete(f *Field) {
	if !f.HasStart {
		f.Start = r.last + 1
	}
	if !f.HasEnd {
		f.End = f.Start
		if f.HasBits {
			f.End = f.Start + f.Bits - 1
		}
	}
	if !f.HasBits {
		f.Bits = f.End - f.Start + 1
	}
}

func (m *Model) split() {
	var word []Piece
	words, row := 0, 1
	for _, f := range m.Fields {
		current := Piece{Field: f.Index, Start: f.Start, End: f.End, Bits: f.Bits, Label: f.Label}
		for int64(len(word)) <= m.BitsPerRow+1 && words < MaxWords {
			piece, next := m.fit(current, row)
			word = append(word, piece)
			if piece.End+1 == int64(row)*m.BitsPerRow {
				m.flush(word, &words)
				word, row = nil, row+1
			}
			if next == nil {
				break
			}
			current = *next
		}
	}
	if len(word) > 0 {
		m.flush(word, &words)
	}
	m.Rows = words
}

func (m *Model) flush(word []Piece, words *int) {
	for _, piece := range word {
		piece.Row = *words
		m.Pieces = append(m.Pieces, piece)
	}
	*words++
}

func (m *Model) fit(block Piece, row int) (Piece, *Piece) {
	limit := int64(row) * m.BitsPerRow
	if block.End+1 <= limit {
		return block, nil
	}
	first := Piece{Field: block.Field, Start: block.Start, End: limit - 1, Label: block.Label, Bits: limit - 1 - block.Start}
	rest := Piece{Field: block.Field, Start: limit, End: block.End, Label: block.Label, Bits: block.End - limit}
	return first, &rest
}
