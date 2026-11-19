package state

import "github.com/gosuda/elegant-mermaid/internal/source"

const None = -1

type Text struct {
	Value string
	Span  source.Span
}

type StateKind uint8

const (
	KindDefault StateKind = iota
	KindFork
	KindJoin
	KindChoice
)

type EndpointRole uint8

const (
	RoleOrdinary EndpointRole = iota
	RoleStart
	RoleEnd
)

type ParentKind uint8

const (
	ParentNone ParentKind = iota
	ParentState
	ParentRegion
)

type Parent struct {
	Kind  ParentKind
	Index int
}

type Occurrence struct {
	Span, IDSpan source.Span
	Scope        int
	Role         EndpointRole
}

type State struct {
	ID           string
	IDSpan       source.Span
	Span         source.Span
	Kind         StateKind
	Descriptions []Text
	Parent       Parent
	Scope        int
	Composite    int
	Classes      []Text
	Styles       []Text
	Note         int
	Occurrences  []Occurrence
}

type Endpoint struct {
	State        int
	Span, IDSpan source.Span
	Scope        int
	Role         EndpointRole
}

type Transition struct {
	From, To  Endpoint
	Label     *Text
	Span      source.Span
	ArrowSpan source.Span
	Scope     int
}

type Composite struct {
	State                     int
	Scope                     int
	Span, OpenSpan, CloseSpan source.Span
	Children                  []int
	Regions                   []int
}

type Region struct {
	ID        string
	Parent    int
	Scope     int
	Span      source.Span
	Separator *source.Span
	Children  []int
}

type Scope struct {
	ID            string
	Parent        int
	Direction     string
	DirectionSpan *source.Span
}

type Note struct {
	Target                         int
	Position                       string
	Text                           Text
	Span, TargetSpan, PositionSpan source.Span
	Scope                          int
}

type ClassDefinition struct {
	ID         string
	IDSpan     source.Span
	Span       source.Span
	Styles     []Text
	TextStyles []Text
}

type Link struct {
	Target     string
	TargetSpan source.Span
	URL        Text
	Tooltip    *Text
	Span       source.Span
	Scope      int
}

type Directive struct {
	Span       source.Span
	Scope      int
	TokenSpans []source.Span
}

type StatementOccurrence struct {
	ID              string
	From, To, Label string
	Span            source.Span
	Body            []StatementOccurrence
	HasBody         bool
	StatementCount  int
}

type Model struct {
	States           []State
	Composites       []Composite
	Regions          []Region
	Transitions      []Transition
	Notes            []Note
	ClassDefinitions []ClassDefinition
	Scopes           []Scope
	Links            []Link
	AccTitle         *Text
	AccDescr         *Text
	Directives       []Directive
	Occurrences      []StatementOccurrence
}

func (m *Model) Title() string {
	if m.AccTitle == nil {
		return ""
	}
	return m.AccTitle.Value
}

func (m *Model) Description() string {
	if m.AccDescr == nil {
		return ""
	}
	return m.AccDescr.Value
}
