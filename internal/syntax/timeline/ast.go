package timeline

import "github.com/gosuda/elegant-mermaid/internal/source"

const (
	kindTimeline   = "timeline"
	kindTimelineLR = "timeline_lr"
	kindTimelineTD = "timeline_td"
	kindNewline    = "NEWLINE"
	kindTitle      = "title"
	kindAccTitle   = "acc_title"
	kindAccTitleV  = "acc_title_value"
	kindAccDescr   = "acc_descr"
	kindAccDescrV  = "acc_descr_value"
	kindAccBlockV  = "acc_descr_multiline_value"
	kindSection    = "section"
	kindEvent      = "event"
	kindPeriod     = "period"
	kindEOF        = "EOF"
	kindInvalid    = "INVALID"
	kindOpen       = "UNTERMINATED"
)

type Token struct {
	Kind    string
	Text    string
	Value   string
	Span    source.Span
	Payload source.Span
	Open    source.Span
	Close   source.Span
}

type Start struct {
	Span     source.Span
	Header   TimelineHeader
	Document Document
}

type TimelineHeader struct {
	Token     Token
	Direction string
}

type Document struct {
	Span  source.Span
	Lines []Line
}

type Line struct {
	Span      source.Span
	Separator *Token
	Statement *Statement
}

type Statement struct {
	Span source.Span
	Kind StatementKind
}

type StatementKind interface {
	statementKind()
}

type Title struct{ Token Token }

type AccTitle struct{ Opener, Value Token }

type AccDescr struct{ Opener, Value Token }

type AccDescrBlock struct{ Value Token }

type Section struct{ Token Token }

type PeriodStatement struct{ Token Token }

type EventStatement struct{ Token Token }

func (*Title) statementKind()           {}
func (*AccTitle) statementKind()        {}
func (*AccDescr) statementKind()        {}
func (*AccDescrBlock) statementKind()   {}
func (*Section) statementKind()         {}
func (*PeriodStatement) statementKind() {}
func (*EventStatement) statementKind()  {}
