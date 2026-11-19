package gantt

import "github.com/gosuda/elegant-mermaid/internal/source"

const (
	KindGantt             = "gantt"
	KindNewline           = "NL"
	KindDateFormat        = "dateFormat"
	KindInclusiveEndDates = "inclusiveEndDates"
	KindTopAxis           = "topAxis"
	KindAxisFormat        = "axisFormat"
	KindTickInterval      = "tickInterval"
	KindIncludes          = "includes"
	KindExcludes          = "excludes"
	KindTodayMarker       = "todayMarker"
	KindWeekdayPrefix     = "weekday_"
	KindWeekendPrefix     = "weekend_"
	KindDate              = "date"
	KindTitle             = "title"
	KindAccDescription    = "accDescription"
	KindSection           = "section"
	KindTaskText          = "taskTxt"
	KindTaskData          = "taskData"
	KindColon             = ":"
	KindAccTitle          = "acc_title"
	KindAccTitleValue     = "acc_title_value"
	KindAccDescr          = "acc_descr"
	KindAccDescrValue     = "acc_descr_value"
	KindAccBlockValue     = "acc_descr_multiline_value"
	KindClick             = "click"
	KindHref              = "href"
	KindCallbackName      = "callbackname"
	KindCallbackArgs      = "callbackargs"
	KindEOF               = "EOF"
	KindInvalid           = "INVALID"
	kindOpen              = "UNTERMINATED"
)

var weekdays = [...]string{"monday", "tuesday", "wednesday", "thursday", "friday", "saturday", "sunday"}

var weekends = [...]string{"friday", "saturday"}

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
	Header   Token
	Document Document
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

type DateFormat struct{ Token Token }

type InclusiveEndDates struct{ Token Token }

type TopAxis struct{ Token Token }

type AxisFormat struct{ Token Token }

type TickInterval struct{ Token Token }

type Excludes struct{ Token Token }

type Includes struct{ Token Token }

type TodayMarker struct{ Token Token }

type Weekday struct {
	Token Token
	Name  string
}

type Weekend struct {
	Token Token
	Name  string
}

type Title struct{ Token Token }

type Section struct{ Token Token }

type AccTitle struct{ Opener, Value Token }

type AccDescr struct{ Opener, Value Token }

type AccDescrBlock struct{ Value Token }

type Task struct{ Text, Data Token }

type ClickStatement struct {
	Click    Token
	Callback *Token
	Args     *Token
	Href     *Token
	Order    []string
}

func (*DateFormat) statementKind()        {}
func (*InclusiveEndDates) statementKind() {}
func (*TopAxis) statementKind()           {}
func (*AxisFormat) statementKind()        {}
func (*TickInterval) statementKind()      {}
func (*Excludes) statementKind()          {}
func (*Includes) statementKind()          {}
func (*TodayMarker) statementKind()       {}
func (*Weekday) statementKind()           {}
func (*Weekend) statementKind()           {}
func (*Title) statementKind()             {}
func (*Section) statementKind()           {}
func (*AccTitle) statementKind()          {}
func (*AccDescr) statementKind()          {}
func (*AccDescrBlock) statementKind()     {}
func (*Task) statementKind()              {}
func (*ClickStatement) statementKind()    {}
