package icon

type shapeKind uint8

const (
	shapeRect shapeKind = iota
	shapeEllipse
	shapeFilledEllipse
	shapeLine
	shapeStroke
	shapeFill
)

type shape struct {
	kind shapeKind
	args []string
}

func rect(x, y, w, h, r string) shape { return shape{shapeRect, []string{x, y, w, h, r}} }

func ellipse(cx, cy, rx, ry string) shape { return shape{shapeEllipse, []string{cx, cy, rx, ry}} }

func disc(cx, cy, rx, ry string) []shape {
	return []shape{{shapeFilledEllipse, []string{cx, cy, rx, ry}}, ellipse(cx, cy, rx, ry)}
}

func dot(cx, cy, r string) shape { return shape{shapeFilledEllipse, []string{cx, cy, r, r}} }

func line(x1, y1, x2, y2 string) shape { return shape{shapeLine, []string{x1, y1, x2, y2}} }

func stroke(d string) shape { return shape{shapeStroke, []string{d}} }

func fill(d string) shape { return shape{shapeFill, []string{d}} }

func join(groups ...[]shape) []shape {
	var out []shape
	for _, g := range groups {
		out = append(out, g...)
	}
	return out
}

func serverRow(y string) []shape {
	d := "m56.25," + y + "c0,.27-.45.5-1,.5h-10.5c-.55,0-1-.23-1-.5s.45-.5,1-.5h10.5c.55,0,1,.23,1,.5Z"
	return []shape{fill(d), stroke(d), dot("32.5", y, ".75"), dot("27.5", y, ".75"), dot("22.5", y, ".75")}
}

func diskScrew(cx, cy string) shape { return ellipse(cx, cy, ".8", ".83") }

const cylinderRim = "c0,3.94,8.95,7.14,20,7.14s20-3.2,20-7.14"

var builtins = map[string][]shape{
	"database": {
		stroke("m20,57.86" + cylinderRim), stroke("m20,45.95" + cylinderRim), stroke("m20,34.05" + cylinderRim),
		ellipse("40", "22.14", "20", "7.14"), line("20", "57.86", "20", "22.14"), line("60", "57.86", "60", "22.14"),
	},
	"server": join(
		[]shape{rect("17.5", "17.5", "45", "45", "2"), line("17.5", "32.5", "62.5", "32.5"), line("17.5", "47.5", "62.5", "47.5")},
		serverRow("25"), serverRow("40"), serverRow("55"),
	),
	"disk": join(
		[]shape{rect("20", "15", "40", "50", "1"), diskScrew("24", "19.17"), diskScrew("56", "19.17"), diskScrew("24", "60.83"), diskScrew("56", "60.83"), ellipse("40", "33.75", "14", "14.58")},
		disc("40", "33.75", "4", "4.17"),
		[]shape{fill("m37.51,42.52l-4.83,13.22c-.26.71-1.1,1.02-1.76.64l-4.18-2.42c-.66-.38-.81-1.26-.33-1.84l9.01-10.8c.88-1.05,2.56-.08,2.09,1.2Z")},
	),
	"internet": {
		ellipse("40", "40", "22.5", "22.5"), line("40", "17.5", "40", "62.5"), line("17.5", "40", "62.5", "40"),
		stroke("m39.99,17.51c-15.28,11.1-15.28,33.88,0,44.98"), stroke("m40.01,17.51c15.28,11.1,15.28,33.88,0,44.98"),
		line("19.75", "30.1", "60.25", "30.1"), line("19.75", "49.9", "60.25", "49.9"),
	},
	"cloud": {
		stroke("m65,47.5c0,2.76-2.24,5-5,5H20c-2.76,0-5-2.24-5-5,0-1.87,1.03-3.51,2.56-4.36-.04-.21-.06-.42-.06-.64,0-2.6,2.48-4.74,5.65-4.97,1.65-4.51,6.34-7.76,11.85-7.76.86,0,1.69.08,2.5.23,2.09-1.57,4.69-2.5,7.5-2.5,6.1,0,11.19,4.38,12.28,10.17,2.14.56,3.72,2.51,3.72,4.83,0,.03,0,.07-.01.1,2.29.46,4.01,2.48,4.01,4.9Z"),
	},
}

const unknownName = "unknown"

func builtinNames() []string {
	return []string{"cloud", "database", "disk", "internet", "server", unknownName}
}
