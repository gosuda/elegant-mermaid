package chart

const KindRadar Kind = "radar"

type Graticule uint8

const (
	GraticuleCircle Graticule = iota
	GraticulePolygon
)

type Radar struct {
	Axes       []string
	Curves     []RadarCurve
	ShowLegend bool
	Ticks      Number
	HasMax     bool
	Max        Number
	Min        Number
	Graticule  Graticule
}

type RadarCurve struct {
	Label  string
	Values []Number
}
