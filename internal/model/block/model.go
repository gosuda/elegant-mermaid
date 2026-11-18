package block

import (
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/block"
)

const (
	codeStyleTarget        = "block/style-target-unknown"
	codeWidthExceeds       = "block/width-exceeds-columns"
	AutoColumns      int32 = -1
)

type Block struct {
	ID         string
	Type       string
	Label      string
	Span       int32
	SizeSpan   source.Span
	IDSpan     source.Span
	Columns    int32
	Directions []string
	Children   []*Block
	Classes    []string
	Styles     []string
}

type Edge struct {
	Start      string
	End        string
	Label      string
	Span       source.Span
	Thickness  string
	Pattern    string
	ArrowStart string
	ArrowEnd   string
}

type ClassDef struct {
	ID         string
	Styles     []string
	TextStyles []string
}

type ConfigEntry struct {
	Key   string
	Value int64
}

type Model struct {
	Root    *Block
	Edges   []Edge
	Classes []ClassDef
	Config  []ConfigEntry
}

func (m *Model) Find(id string) *Block {
	return find(m.Root, id)
}

func find(block *Block, id string) *Block {
	for _, child := range block.Children {
		if child.ID == id {
			return child
		}
		if found := find(child, id); found != nil {
			return found
		}
	}
	return nil
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := newResolver(src, document)
	r.document(r.model.Root, document.Document)
	r.model.Edges = slices.DeleteFunc(r.model.Edges, func(e Edge) bool {
		return find(r.model.Root, e.Start) == nil || find(r.model.Root, e.End) == nil
	})
	return r.model, r.diags
}

func readPadding(model *Model, block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == "block" })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		if field.Key != "padding" || field.Value.Kind != syntax.ValueInteger {
			continue
		}
		if value, ok := parseNonNegative(field.Value.Text); ok {
			model.Config = []ConfigEntry{{Key: "padding", Value: value}}
		}
	}
}

func parseNonNegative(text string) (int64, bool) {
	var value int64
	for i := range len(text) {
		c := text[i]
		if c < '0' || c > '9' || value > maxPadding {
			return 0, false
		}
		value = value*10 + int64(c-'0')
	}
	return value, len(text) > 0 && value <= maxPadding
}

const maxPadding = 1024
