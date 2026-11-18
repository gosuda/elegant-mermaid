package flowchart

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
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

type Decl struct {
	ID       source.Span
	Label    string
	HasLabel bool
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
	Decls     []Decl
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

type ClickKind uint8

const (
	ClickLink ClickKind = iota
	ClickCallback
)

type Click struct {
	Target     string
	Kind       ClickKind
	Callback   string
	Args       string
	Tip        string
	URL        string
	Href       bool
	Span       source.Span
	ActionSpan source.Span
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

	SubgraphCollisions []source.Span
	UnquotedAtSpans    []source.Span
}

type TypedShape struct {
	Value string
	Span  source.Span
}

func resolveLabel(text string) string {
	out := strings.TrimSpace(text)
	if len(out) >= 2 && out[0] == '"' && out[len(out)-1] == '"' {
		out = out[1 : len(out)-1]
	}
	return syntax.DecodeEntities(out)
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
