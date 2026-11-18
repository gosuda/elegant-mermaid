package agentflow

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Start struct {
	Span     source.Span
	Header   Token
	Config   GraphConfig
	Document Document
}

type GraphConfig struct {
	Span      source.Span
	Direction Direction
	Authored  *Token
	Separator *FirstStmtSeparator
}

type Document struct {
	Span  source.Span
	Lines []Line
}

type Line struct {
	Span      source.Span
	Statement *Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind struct {
	Flow      *FlowStatement
	Global    *GlobalStatement
	Connector *ConnectorStatement
	Vertex    *VertexStatement
	ClassDef  *ClassDefStatement
	Class     *ClassStatement
	Style     *StyleStatement
	LinkStyle *LinkStyleStatement
	Click     *ClickStatement
	Direction *Direction
	Access    *Accessibility
}

type FlowStatement struct {
	Name     *TextNoTags
	Title    *Text
	Metadata []ShapeData
	Opening  source.Span
	Body     Document
	Close    source.Span
}

type GlobalStatement struct {
	Opening source.Span
	Body    Document
	Close   source.Span
}

type ConnectorStatement struct {
	Name     TextNoTags
	Title    *Text
	Metadata []ShapeData
}

type Accessibility struct {
	Title bool
	Value Token
}

type VertexStatement struct {
	Span  source.Span
	Nodes []Node
	Links []Link
}

type Node struct {
	Span     source.Span
	Vertices []StyledVertex
}

type StyledVertex struct {
	Span     source.Span
	Vertex   Vertex
	Class    *IdString
	Metadata []ShapeData
}

type Vertex struct {
	Span       source.Span
	ID         IdString
	Label      *Text
	Shape      string
	Delimiters *[2]source.Span
	Property   *[2]Token
}

type ShapeData struct {
	Span   source.Span
	Pieces []Token
	Value  string
}

func (d ShapeData) NormalizedValue() string {
	if !hasQuotedLinebreak(d.Value) {
		return d.Value
	}
	var out strings.Builder
	out.Grow(len(d.Value))
	quoted := false
	rest := d.Value
	for len(rest) > 0 {
		c, size := decodeRune(rest)
		rest = rest[size:]
		if c == '"' {
			quoted = !quoted
		}
		if !quoted || (c != '\r' && c != '\n') {
			out.WriteRune(c)
			continue
		}
		out.WriteString("<br/>")
		for len(rest) > 0 {
			n, s := decodeRune(rest)
			if !isWhitespace(n) {
				break
			}
			rest = rest[s:]
		}
	}
	return out.String()
}

func hasQuotedLinebreak(value string) bool {
	quoted := false
	for _, c := range value {
		if c == '"' {
			quoted = !quoted
		}
		if quoted && (c == '\r' || c == '\n') {
			return true
		}
	}
	return false
}

type Link struct {
	Span      source.Span
	Statement LinkStatement
	Opening   *Token
	ArrowText *ArrowText
	EdgeText  *EdgeText
}

func (l *Link) Label() *Text {
	if l.ArrowText != nil {
		return &l.ArrowText.Text
	}
	if l.EdgeText != nil {
		return &l.EdgeText.Text
	}
	return nil
}

type LinkStatement struct {
	Span     source.Span
	ID       *Token
	Operator Token
}

type ArrowText struct {
	Span source.Span
	Text Text
}

type EdgeText struct {
	Span source.Span
	Text Text
}

type TextKind uint8

const (
	TextPlain TextKind = iota
	TextString
	TextMarkdown
)

type Text struct {
	Span   source.Span
	Pieces []Token
	Kind   TextKind
}

type TextNoTags struct {
	Span   source.Span
	Pieces []Token
	Kind   TextKind
}

type IdString struct {
	Span   source.Span
	Tokens []Token
}

type AlphaNum struct {
	Span   source.Span
	Tokens []Token
}

type ClassDefStatement struct {
	Span   source.Span
	ID     IdString
	Styles StylesOpt
}

type ClassStatement struct {
	Span    source.Span
	Targets IdString
	Class   IdString
}

type StyleStatement struct {
	Span    source.Span
	Targets IdString
	Styles  StylesOpt
}

type LinkStyleStatement struct {
	Span          source.Span
	Default       *Token
	Indices       *NumList
	Interpolation *AlphaNum
	Styles        *StylesOpt
}

type NumList struct {
	Span    source.Span
	Indices []Token
}

type StylesOpt struct {
	Span   source.Span
	Styles []Style
}

type Style struct {
	Span       source.Span
	Components []StyleComponent
}

type StyleComponent struct {
	Span  source.Span
	Token Token
}

type ClickStatement struct {
	Span      source.Span
	ID        Token
	Callback  *AlphaNum
	Arguments *Token
	URL       *Token
	Tooltip   *Token
	Target    *Token
}

type Direction struct {
	Span  source.Span
	Value string
}

type FirstStmtSeparator struct {
	Span   source.Span
	Tokens []Token
}
