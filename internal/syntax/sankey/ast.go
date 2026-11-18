package sankey

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span   source.Span
	Header Token
	Csv    Csv
	OptEof OptEof
}

type Csv struct {
	Span    source.Span
	Records []Record
}

type OptEof struct {
	Span    source.Span
	Present bool
}

type Record struct {
	Span   source.Span
	Source Field
	Target Field
	Value  Field
	Index  int
}

type Field struct {
	Span       source.Span
	Escaped    *Escaped
	NonEscaped *NonEscaped
}

type Escaped struct {
	Span source.Span
	Text string
}

type NonEscaped struct {
	Span source.Span
	Text string
}

func (f Field) Text() string {
	if f.Escaped != nil {
		return f.Escaped.Text
	}
	if f.NonEscaped != nil {
		return f.NonEscaped.Text
	}
	return ""
}
