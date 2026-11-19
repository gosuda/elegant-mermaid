package sequence

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Start struct {
	Span     source.Span
	Header   Token
	Document Document
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

type StatementKind interface {
	statementKind()
}

type ParticipantStatement struct {
	Create  *source.Span
	Keyword source.Span
	Draw    string
	Destroy bool
	Actor   Actor
	Alias   *Alias
	Config  *ConfigObject
}

type Alias struct {
	Token Token
	Text  Text2
}

type ConfigObject struct {
	Span        source.Span
	Content     string
	ContentSpan source.Span
}

type Actor struct {
	Span source.Span
	Text string
}

type Signal struct {
	Span         source.Span
	Source       Actor
	CentralStart bool
	Arrow        Token
	Suffix       *Token
	CentralEnd   bool
	Target       Actor
	Text         Text2
}

type Autonumber struct {
	Span    source.Span
	Start   *Token
	Step    *Token
	Off     bool
	OffSpan source.Span
}

type Activate struct {
	Span    source.Span
	Keyword source.Span
	Actor   Actor
}

type Deactivate struct {
	Span    source.Span
	Keyword source.Span
	Actor   Actor
}

type NoteStatement struct {
	Span      source.Span
	Placement source.Span
	Over      bool
	Actors    []Actor
	Text      Text2
}

type Links struct {
	Span    source.Span
	Keyword source.Span
	Actor   Actor
	Text    Text2
}

type Link struct {
	Span    source.Span
	Keyword source.Span
	Actor   Actor
	Text    Text2
}

type Properties struct {
	Span    source.Span
	Keyword source.Span
	Actor   Actor
	Text    Text2
}

type Details struct {
	Span    source.Span
	Keyword source.Span
	Actor   Actor
	Text    Text2
}

type Title struct {
	Span   source.Span
	Legacy bool
	Value  string
}

type Accessibility struct {
	Span  source.Span
	Title bool
	Value source.Span
}

type Text2 struct {
	Span source.Span
	Text string
}

type BoxBlock struct {
	Span    source.Span
	Keyword source.Span
	Text    Text2
	Section BoxSection
	Close   Token
}

type BoxSection struct {
	Span  source.Span
	Lines []Line
}

type ControlBlock struct {
	Span     source.Span
	Keyword  source.Span
	Kind     string
	Text     Text2
	Sections []Section
	Close    Token
}

type Section struct {
	Separator *Token
	Title     Text2
	Document  Document
}

func (*ParticipantStatement) statementKind() {}
func (*Signal) statementKind()               {}
func (*Autonumber) statementKind()           {}
func (*Activate) statementKind()             {}
func (*Deactivate) statementKind()           {}
func (*NoteStatement) statementKind()        {}
func (*Links) statementKind()                {}
func (*Link) statementKind()                 {}
func (*Properties) statementKind()           {}
func (*Details) statementKind()              {}
func (*Title) statementKind()                {}
func (*Accessibility) statementKind()        {}
func (*BoxBlock) statementKind()             {}
func (*ControlBlock) statementKind()         {}
