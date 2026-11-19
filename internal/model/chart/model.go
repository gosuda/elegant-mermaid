package chart

type Kind string

const KindXYChart Kind = "xychart"

type Number int64

type DumpKind uint8

const (
	DumpBool DumpKind = iota
	DumpInteger
	DumpString
)

type DumpValue struct {
	Kind    DumpKind
	Bool    bool
	Integer int64
	String  string
}

type ConfigEntry struct {
	Key   string
	Value DumpValue
}

type Chart struct {
	Kind    Kind
	Title   string
	Config  []ConfigEntry
	XY      *XY
	Gantt   *Gantt
	Radar   *Radar
	Treemap *Treemap
	Pie     *Pie
	Venn    *Venn
	Sankey  *Sankey
}

func (c *Chart) Integer(key string) (int64, bool) {
	for _, e := range c.Config {
		if e.Key == key && e.Value.Kind == DumpInteger {
			return e.Value.Integer, true
		}
	}
	return 0, false
}

func (c *Chart) Bool(key string) (value, found bool) {
	for _, e := range c.Config {
		if e.Key == key && e.Value.Kind == DumpBool {
			return e.Value.Bool, true
		}
	}
	return false, false
}

func (c *Chart) String(key string) (string, bool) {
	for _, e := range c.Config {
		if e.Key == key && e.Value.Kind == DumpString {
			return e.Value.String, true
		}
	}
	return "", false
}

type Orientation uint8

const (
	OrientationVertical Orientation = iota
	OrientationHorizontal
)

type XY struct {
	Orientation Orientation
	XTitle      string
	YTitle      string
	XAxis       XAxis
	YAxis       YAxis
	Plots       []Plot
}

type XAxis struct {
	Band       bool
	Categories []string
	Min, Max   Number
}

type YAxis struct {
	Min, Max Number
}

type PlotKind uint8

const (
	PlotBar PlotKind = iota
	PlotLine
)

type Point struct {
	Present bool
	Slot    int
	HasX    bool
	X       Number
	Value   Number
	Label   string
}

type Plot struct {
	Kind   PlotKind
	Title  string
	Points []Point
}
