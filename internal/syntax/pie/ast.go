package pie

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type EOL struct {
	Span source.Span
}

type Pie struct {
	Span     source.Span
	Header   Token
	ShowData bool
	Body     []Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type PieSection struct {
	Label  Token
	Number Token
	EOL    EOL
}

type Metadata struct {
	Field string
	Value string
	Span  source.Span
	EOL   EOL
}

type TitleAndAccessibilities struct {
	Items []Metadata
}

func (*PieSection) statementKind()              {}
func (*TitleAndAccessibilities) statementKind() {}
