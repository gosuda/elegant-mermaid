package scene

import (
	"encoding/json"
	"errors"
	"math"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type Metrics struct {
	Schema           int   `json:"schema"`
	HardOK           bool  `json:"hard_ok"`
	Nodes            int64 `json:"nodes"`
	MeanNodeExtent   int64 `json:"mean_node_extent"`
	Crossings        int64 `json:"crossings"`
	Bends            int64 `json:"bends"`
	AgainstFlowEdges int64 `json:"against_flow_edges"`
	TotalRouteLength int64 `json:"total_route_length"`
	CanvasArea       int64 `json:"canvas_area"`
	SoftCost         int64 `json:"soft_cost"`
}

func (m Metrics) AppendJSON(dst []byte) []byte {
	dst = append(dst, `{"schema":1,"hard_ok":`...)
	dst = strconv.AppendBool(dst, m.HardOK)
	names := [...]string{"nodes", "mean_node_extent", "crossings", "bends", "against_flow_edges", "total_route_length", "canvas_area", "soft_cost"}
	values := [...]int64{m.Nodes, m.MeanNodeExtent, m.Crossings, m.Bends, m.AgainstFlowEdges, m.TotalRouteLength, m.CanvasArea, m.SoftCost}
	for i, name := range names {
		dst = append(dst, ',', '"')
		dst = append(dst, name...)
		dst = append(dst, '"', ':')
		dst = strconv.AppendInt(dst, values[i], 10)
	}
	return append(dst, '}', '\n')
}

type metricArithmetic struct{ err error }

func (a *metricArithmetic) add(x, y int64) int64 {
	if (y > 0 && x > math.MaxInt64-y) || (y < 0 && x < math.MinInt64-y) {
		a.err = geom.ErrOverflow
		return 0
	}
	return x + y
}
func (a *metricArithmetic) mul(x, y int64) int64 {
	if x == 0 || y == 0 {
		return 0
	}
	if metricProductOverflows(x, y) {
		a.err = geom.ErrOverflow
		return 0
	}
	return x * y
}
func metricProductOverflows(x, y int64) bool {
	if x > 0 {
		if y > 0 {
			return x > math.MaxInt64/y
		}
		return y < math.MinInt64/x
	}
	if y > 0 {
		return x < math.MinInt64/y
	}
	return x < math.MaxInt64/y
}
func (m Metrics) Cost() (int64, error) {
	a := metricArithmetic{}
	den := a.mul(a.mul(m.MeanNodeExtent, m.MeanNodeExtent), max(int64(1), m.Nodes))
	score := a.add(a.add(a.mul(10, m.Crossings), a.mul(2, m.Bends)), a.mul(5, m.AgainstFlowEdges))
	if a.err != nil {
		return 0, a.err
	}
	score = a.add(score, m.TotalRouteLength/m.MeanNodeExtent)
	score = a.add(score, m.CanvasArea/den)
	return score, a.err
}

func MeasureMetrics(d *Dump, refused int) (Metrics, error) {
	m := Metrics{Schema: 1, MeanNodeExtent: 1}
	ok, err := d.Check()
	if err != nil {
		return m, err
	}
	m.HardOK = ok && refused == 0
	a := metricArithmetic{}
	var sum int64
	for _, b := range d.Boxes {
		if b.Role == RoleNode {
			m.Nodes++
			sum = a.add(sum, (int64(b.Rect.W)+int64(b.Rect.H))/2)
		}
	}
	m.MeanNodeExtent = max(int64(1), sum/max(int64(1), m.Nodes))
	if a.err != nil {
		return m, a.err
	}
	if err := metricRoutes(d, &m, &a); err != nil {
		return m, err
	}
	m.CanvasArea = metricArea(d, &a)
	if a.err != nil {
		return m, a.err
	}
	m.SoftCost, err = m.Cost()
	return m, err
}
func metricRoutes(d *Dump, m *Metrics, a *metricArithmetic) error {
	routes := make([][]geom.Point, len(d.Routes))
	for i, r := range d.Routes {
		routes[i] = metricPoints(r.Points)
		if err := metricPath(routes[i], m, a); err != nil {
			return err
		}
		m.AgainstFlowEdges += metricAgainst(d, r)
		for j := range i {
			m.Crossings = a.add(m.Crossings, metricCrossings(routes[i], routes[j], a))
		}
	}
	return a.err
}
func metricPoints(points []geom.Point) []geom.Point {
	out := make([]geom.Point, 0, len(points))
	for _, p := range points {
		if len(out) == 0 || out[len(out)-1] != p {
			out = append(out, p)
		}
	}
	return out
}
func metricCross(a, b, c geom.Point, ar *metricArithmetic) int64 {
	x, y := int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y)
	u, v := int64(c.X)-int64(a.X), int64(c.Y)-int64(a.Y)
	return ar.add(ar.mul(x, v), -ar.mul(y, u))
}
func metricSign(n int64) int64 {
	if n < 0 {
		return -1
	}
	if n > 0 {
		return 1
	}
	return 0
}
func metricCrossings(p, q []geom.Point, a *metricArithmetic) int64 {
	var n int64
	for i := 1; i < len(p); i++ {
		for j := 1; j < len(q); j++ {
			x := metricSign(metricCross(p[i-1], p[i], q[j-1], a)) * metricSign(metricCross(p[i-1], p[i], q[j], a))
			y := metricSign(metricCross(q[j-1], q[j], p[i-1], a)) * metricSign(metricCross(q[j-1], q[j], p[i], a))
			if x == -1 && y == -1 {
				n = a.add(n, 1)
			}
		}
	}
	return n
}
func metricPath(p []geom.Point, m *Metrics, a *metricArithmetic) error {
	for i := 1; i < len(p); i++ {
		dx, dy := int64(p[i].X)-int64(p[i-1].X), int64(p[i].Y)-int64(p[i-1].Y)
		squared := a.add(a.mul(dx, dx), a.mul(dy, dy))
		if a.err != nil {
			return a.err
		}
		length, err := geom.Isqrt(squared)
		if err != nil {
			return err
		}
		m.TotalRouteLength = a.add(m.TotalRouteLength, length)
		if i > 1 && metricBend(p[i-2], p[i-1], p[i], a) {
			m.Bends = a.add(m.Bends, 1)
		}
	}
	return a.err
}
func metricBend(p, q, r geom.Point, a *metricArithmetic) bool {
	dx, dy := int64(q.X)-int64(p.X), int64(q.Y)-int64(p.Y)
	ex, ey := int64(r.X)-int64(q.X), int64(r.Y)-int64(q.Y)
	return metricCross(p, q, r, a) != 0 || a.add(a.mul(dx, ex), a.mul(dy, ey)) < 0
}
func metricAgainst(d *Dump, r Route) int64 {
	var from, to int64
	for _, b := range d.Boxes {
		c := 2*int64(b.Rect.Y) + int64(b.Rect.H)
		if d.Options.Direction == DirectionLR || d.Options.Direction == DirectionRL {
			c = 2*int64(b.Rect.X) + int64(b.Rect.W)
		}
		if b.ID == r.From {
			from = c
		}
		if b.ID == r.To {
			to = c
		}
	}
	sign := int64(1)
	if d.Options.Direction == DirectionBT || d.Options.Direction == DirectionRL {
		sign = -1
	}
	if sign*(to-from) < 0 {
		return 1
	}
	return 0
}
func metricArea(d *Dump, a *metricArithmetic) int64 {
	var left, top, right, bottom int64
	set := false
	point := func(x, y int64) {
		if !set {
			left, top, right, bottom = x, y, x, y
			set = true
		}
		left = min(left, x)
		top = min(top, y)
		right = max(right, x)
		bottom = max(bottom, y)
	}
	rect := func(r geom.Rect) { point(int64(r.X), int64(r.Y)); point(int64(r.X)+int64(r.W), int64(r.Y)+int64(r.H)) }
	for _, b := range d.Boxes {
		rect(b.Rect)
	}
	for _, l := range d.Labels {
		rect(l.Rect)
	}
	for _, r := range d.Routes {
		for _, p := range r.Points {
			point(int64(p.X), int64(p.Y))
		}
	}
	return a.mul(right-left, bottom-top)
}

type metricRectJSON struct{ X, Y, W, H int32 }

func (r metricRectJSON) rect() geom.Rect { return geom.Rect{X: r.X, Y: r.Y, W: r.W, H: r.H} }
func ReadMetricDump(data []byte) (Dump, error) {
	var wire struct {
		Version              int
		Stage, Kind, Profile string
		Options              struct{ Direction string }
		Canvas               struct{ W, H int32 }
		Boxes                []struct {
			metricRectJSON
			ID, Role, Parent string
			Exclusive        bool
		}
		Routes []struct {
			ID, From, To string
			Orthogonal   bool
			Points       [][2]int32
		}
		Labels []struct {
			metricRectJSON
			ID, Owner, Text string
			Lines           []string
		}
	}
	if err := json.Unmarshal(data, &wire); err != nil {
		return Dump{}, err
	}
	direction, ok := ParseDirection(wire.Options.Direction)
	if !metricHeaderValid(wire.Version, wire.Stage, wire.Profile) || !ok {
		return Dump{}, errors.New("malformed layout dump")
	}
	d := Dump{Kind: wire.Kind, Options: DefaultOptions(), Canvas: geom.Size{W: wire.Canvas.W, H: wire.Canvas.H}}
	d.Options.Direction = direction
	for _, b := range wire.Boxes {
		role := RoleNode
		if b.Role == "group" {
			role = RoleGroup
		} else if b.Role != "node" {
			return Dump{}, errors.New("malformed box role")
		}
		d.Boxes = append(d.Boxes, Box{ID: b.ID, Role: role, Rect: b.rect(), Parent: b.Parent, Exclusive: b.Exclusive})
	}
	for _, r := range wire.Routes {
		route := Route{ID: r.ID, From: r.From, To: r.To, Orthogonal: r.Orthogonal}
		for _, p := range r.Points {
			route.Points = append(route.Points, geom.Point{X: p[0], Y: p[1]})
		}
		d.Routes = append(d.Routes, route)
	}
	for _, l := range wire.Labels {
		d.Labels = append(d.Labels, Label{ID: l.ID, Owner: l.Owner, Text: l.Text, Rect: l.rect(), Lines: l.Lines})
	}
	return d, nil
}

func metricHeaderValid(version int, stage, profile string) bool {
	return version == 1 && stage == "layout" && profile == "vector"
}
