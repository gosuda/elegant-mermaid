package gantt

import (
	chartmodel "github.com/gosuda/elegant-mermaid/internal/model/chart"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	NoSection       = -1
	DefaultWeekday  = "sunday"
	DefaultWeekend  = "saturday"
	DefaultAxisForm = "%Y-%m-%d"
	DayAxisForm     = "%d"
	configKey       = "gantt"
)

type Operand struct {
	Text string
	Span source.Span
}

type Section struct {
	Name  string
	Label string
	Span  source.Span
}

type RowKind uint8

const (
	RowSection RowKind = iota
	RowTask
)

type Row struct {
	Kind  RowKind
	Index int
}

type Task struct {
	Text      string
	Label     string
	Section   int
	ID        string
	Generated bool
	Active    bool
	Done      bool
	Crit      bool
	Milestone bool
	Vert      bool
	Order     int
	Start     Operand
	End       Operand
	PrevID    string
	HasPrev   bool
	Span      source.Span
	DataSpan  source.Span

	StartKind    startKind
	HasStart     bool
	HasEnd       bool
	StartSeconds int64
	EndSeconds   int64
	RenderEnd    int64
	HasRenderEnd bool
	ManualEnd    bool
	Resolved     bool
	Failed       bool
	Link         string
	HasLink      bool
}

type startKind uint8

const (
	startOperand startKind = iota
	startPrevEnd
)

type Callback struct {
	Name string
	Args []string
	Span source.Span
}

type Click struct {
	IDs      string
	Callback *Callback
	Href     string
	HrefSpan source.Span
	HasHref  bool
	Span     source.Span
}

type Model struct {
	AccTitle string
	AccDescr string

	Title      string
	TitleLabel string

	DateFormat       string
	AxisFormat       string
	AxisFormatSpan   source.Span
	TickInterval     string
	TickIntervalSpan source.Span
	HasTickInterval  bool
	TodayMarker      string
	HasTodayMarker   bool
	InclusiveEnd     bool
	TopAxis          bool
	Weekday          string
	WeekdaySet       bool
	Weekend          string
	Includes         []string
	Excludes         []string

	Sections []Section
	Tasks    []Task
	Rows     []Row
	Clicks   []Click
	Config   []chartmodel.ConfigEntry
}

func (m *Model) ConfigInteger(key string) (int64, bool) {
	for _, e := range m.Config {
		if e.Key == key && e.Value.Kind == chartmodel.DumpInteger {
			return e.Value.Integer, true
		}
	}
	return 0, false
}

func (m *Model) ConfigString(key string) (string, bool) {
	for _, e := range m.Config {
		if e.Key == key && e.Value.Kind == chartmodel.DumpString {
			return e.Value.String, true
		}
	}
	return "", false
}

func (m *Model) ConfigBool(key string) bool {
	for _, e := range m.Config {
		if e.Key == key && e.Value.Kind == chartmodel.DumpBool {
			return e.Value.Bool
		}
	}
	return false
}

func (m *Model) EffectiveWeekday() string {
	if m.WeekdaySet {
		return m.Weekday
	}
	if name, ok := m.ConfigString("weekday"); ok {
		return name
	}
	return m.Weekday
}

func (m *Model) EffectiveTopAxis() bool { return m.TopAxis || m.ConfigBool("topAxis") }
