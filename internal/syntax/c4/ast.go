package c4

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Span source.Span
	Raw  []byte
}

type Start struct {
	Span       source.Span
	MermaidDoc *MermaidDoc
	Direction  *Direction
}

type Direction struct {
	Span      source.Span
	Direction Token
}

type MermaidDoc struct {
	Span        source.Span
	GraphConfig GraphConfig
}

type GraphConfig struct {
	Span       source.Span
	Header     Token
	Statements Statements
}

type Statement struct {
	Span    source.Span
	Other   *OtherStatement
	Diagram *DiagramStatement
}

type Statements struct {
	Span  source.Span
	Items []Statement
}

type OtherStatement struct {
	Span  source.Span
	Form  string
	Value Token
}

type DiagramStatement struct {
	Span     source.Span
	Call     *CallStatement
	Boundary *BoundaryStatement
}

type CallStatement struct {
	Span       source.Span
	Macro      Token
	Attributes Attributes
}

type BoundaryStatement struct {
	Span  source.Span
	Start BoundaryStartStatement
	Body  DiagramStatements
	Stop  BoundaryStopStatement
}

type BoundaryStartStatement struct {
	Span  source.Span
	Start BoundaryStart
	Brace Token
}

type BoundaryStart struct {
	Span       source.Span
	Macro      Token
	Attributes Attributes
}

type BoundaryStopStatement struct {
	Span  source.Span
	Close Token
}

type DiagramStatements struct {
	Span  source.Span
	Items []Statement
}

type Attributes struct {
	Span  source.Span
	Items []Attribute
}

type Attribute struct {
	Span       source.Span
	Positional *Token
	Key        *Token
	Value      *Token
	Empty      *Token
}
