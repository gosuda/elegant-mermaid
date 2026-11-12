package flowchart

import (
	"sort"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

type LabelKind string

const (
	LabelText LabelKind = "text"

	LabelString LabelKind = "string"

	LabelMarkdown LabelKind = "markdown"
)

type Style struct {
	Text string
	Key  string
	Span source.Span
}

type StylesOpt struct {
	Styles []Style
}

type Node struct {
	ID        string
	Label     string
	LabelKind LabelKind
	Shape     string
	Classes   []string
	Styles    StylesOpt
	First     source.Span
	Span      source.Span
	Attrs     map[string]string
}

type Edge struct {
	From    string
	To      string
	Label   string
	LabelOK bool
	Labels  LabelKind
	Stroke  string
	Marker  string
	Start   string
	Length  int
	UserID  string
	Span    source.Span
	Attrs   map[string]string
}

type Group struct {
	ID        string
	Title     string
	Direction string
	DirSpan   source.Span
	Members   []string
	Parent    string
	Span      source.Span
	View      string
}

type ClassDef struct {
	Names  []string
	Styles StylesOpt
	Span   source.Span
}

type LinkStyle struct {
	Default       bool
	Indices       []int
	Styles        StylesOpt
	Interpolation string
	Span          source.Span
}

type StyleTarget struct {
	ID     string
	Styles StylesOpt
	Span   source.Span
}

type Click struct {
	Target   string
	Callback string
	Args     string
	Tip      string
	URL      string
	Href     bool
	Span     source.Span
}

type Model struct {
	Direction     string
	DirectionSpan source.Span
	Nodes         []Node
	Edges         []Edge
	Groups        []Group
	ClassDefs     []ClassDef
	LinkStyles    []LinkStyle
	StyleTargets  []StyleTarget
	Clicks        []Click
	AccTitle      string
	AccDescr      string
	TypedShapes   []TypedShape
}

type TypedShape struct {
	Value string
	Span  source.Span
}

var entityIndex = buildEntityIndex()

func buildEntityIndex() map[string][]uint32 {
	out := make(map[string][]uint32, len(gen.Entities))
	for _, entity := range gen.Entities {
		out[entity.Name] = entity.CPS
	}
	return out
}

func entityCodePoints(name string) (string, bool) {
	cps, ok := entityIndex[name]
	if !ok {
		return "", false
	}
	var sb strings.Builder
	for _, cp := range cps {
		sb.WriteRune(rune(cp))
	}
	return sb.String(), true
}

func decodeEntities(text string) string {
	var sb strings.Builder
	for i := 0; i < len(text); {
		if text[i] != '#' {
			sb.WriteByte(text[i])
			i++
			continue
		}
		end, decoded, ok := entityAt(text, i)
		if !ok {
			sb.WriteByte(text[i])
			i++
			continue
		}
		sb.WriteString(decoded)
		i = end
	}
	return sb.String()
}

func entityAt(text string, at int) (int, string, bool) {
	end := at + 1
	for end < len(text) && isEntityByte(text[end]) {
		end++
	}
	if end >= len(text) || text[end] != ';' || end == at+1 {
		return at, "", false
	}
	inner := text[at+1 : end]
	if scalar, ok := numericEntity(inner); ok {
		return end + 1, scalar, true
	}
	if cps, ok := entityCodePoints("&" + inner + ";"); ok {
		return end + 1, cps, true
	}
	return at, "", false
}

func isEntityByte(b byte) bool {
	return b >= 'A' && b <= 'Z' || b >= 'a' && b <= 'z' || b >= '0' && b <= '9' || b == '_'
}

func numericEntity(inner string) (string, bool) {
	digits := strings.TrimPrefix(inner, "+")
	if digits == "" {
		return "", false
	}
	value := 0
	for i := range len(digits) {
		if digits[i] < '0' || digits[i] > '9' {
			return "", false
		}
		value = value*10 + int(digits[i]-'0')
		if value > utf8.MaxRune {
			return "", false
		}
	}
	if value == 0 || !utf8.ValidRune(rune(value)) {
		return "", false
	}
	return string(rune(value)), true
}

func resolveLabel(text string) string {
	out := strings.TrimSpace(text)
	if len(out) >= 2 && out[0] == '"' && out[len(out)-1] == '"' {
		out = out[1 : len(out)-1]
	}
	return decodeEntities(out)
}

func labelKindOf(k syn.LabelKind) LabelKind {
	switch k {
	case syn.LabelString:
		return LabelString
	case syn.LabelMarkdown:
		return LabelMarkdown
	}
	return LabelText
}

func resolveStyles(opt syn.StylesOpt) StylesOpt {
	out := StylesOpt{}
	for _, style := range opt.Styles {
		text := style.Text()
		key, _, _ := strings.Cut(text, ":")
		out.Styles = append(out.Styles, Style{Text: text, Key: strings.TrimSpace(key), Span: style.Span})
	}
	return out
}

var _ = sort.Strings
