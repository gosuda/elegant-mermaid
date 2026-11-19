package chart

const KindGantt Kind = "gantt"

type GanttRowKind uint8

const (
	GanttRowSection GanttRowKind = iota
	GanttRowTask
)

type GanttRow struct {
	Kind  GanttRowKind
	Index int
}

type GanttTask struct {
	Label     string
	Section   int
	Start     int64
	End       int64
	RenderEnd int64
	Milestone bool
	Vert      bool
	Crit      bool
	Active    bool
	Done      bool
}

type Gantt struct {
	Sections  []string
	Tasks     []GanttTask
	Rows      []GanttRow
	Excludes  []string
	Includes  []string
	Weekend   string
	Weekday   string
	TopAxis   bool
	TickEvery int64
	TickUnit  string
	AxisForm  string
}
