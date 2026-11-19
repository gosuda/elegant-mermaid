package packet

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span       source.Span
	Header     Token
	Statements []Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type Operand struct {
	Value int64
	Span  source.Span
}

type Label struct {
	Text string
	Span source.Span
}

type PacketBlock struct {
	Start *Operand
	End   *Operand
	Bits  *Operand
	Label Label
}

type Metadata struct {
	Field string
	Value string
}

func (*PacketBlock) statementKind() {}
func (*Metadata) statementKind()    {}
