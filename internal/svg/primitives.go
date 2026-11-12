package svg

import (
	"fmt"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func pair(p geom.Point) string { return number(int64(p.X)) + " " + number(int64(p.Y)) }
func points(ps []geom.Point) string {
	var b strings.Builder
	for i, p := range ps {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString(number(int64(p.X)) + "," + number(int64(p.Y)))
	}
	return b.String()
}
func rectAttrs(p geom.Rect) string {
	return "x='" + number(int64(p.X)) + "' y='" + number(int64(p.Y)) + "' width='" + number(int64(p.W)) + "' height='" + number(int64(p.H)) + "'"
}
func (r *renderer) primitive(p scene.Primitive) (string, error) {
	switch v := p.(type) {
	case *scene.Rect:
		return r.element("rect", v.Shape, rectAttrs(v.Rect))
	case *scene.RoundRect:
		return r.element("rect", v.Shape, rectAttrs(v.Rect)+" rx='"+number(int64(v.R))+"' ry='"+number(int64(v.R))+"'")
	case *scene.Ellipse:
		return r.element("ellipse", v.Shape, fmt.Sprintf("cx='%s' cy='%s' rx='%s' ry='%s'", number(int64(v.CX)), number(int64(v.CY)), number(int64(v.RX)), number(int64(v.RY))))
	case *scene.Polygon:
		return r.element("polygon", v.Shape, "points='"+points(v.Points)+"'")
	case *scene.Polyline:
		if v.Corner > 0 {
			return r.element("path", v.Shape, "d='"+rounded(v.Points, v.Corner)+"'")
		}
		return r.element("polyline", v.Shape, "points='"+points(v.Points)+"'")
	case *scene.Path:
		return r.element("path", v.Shape, "d='"+pathData(v.Commands)+"'")
	case *scene.MarkerRef:
		return r.marker(v)
	case *scene.Text:
		return r.text(v)
	default:
		return "", &ConfigError{"SymbolRef is not a vector primitive"}
	}
}
func (r *renderer) element(tag string, s scene.Shape, geometry string) (string, error) {
	a, e := r.attributes(s)
	if e != nil {
		return "", e
	}
	parts := strings.SplitN(a, " ", 2)
	tail := ""
	if len(parts) > 1 {
		tail = " " + parts[1]
	}
	return "<" + tag + " " + parts[0] + " " + geometry + tail + "/>\n", nil
}
func abs(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}
func direction(a, b geom.Point) (int64, int64, int64) {
	dx, dy := int64(b.X)-int64(a.X), int64(b.Y)-int64(a.Y)
	l := abs(dx) + abs(dy)
	if dx != 0 {
		dx /= abs(dx)
	}
	if dy != 0 {
		dy /= abs(dy)
	}
	return dx, dy, l
}
func rounded(ps []geom.Point, limit int32) string {
	if len(ps) == 0 {
		return ""
	}
	var b strings.Builder
	b.WriteString("M " + pair(ps[0]))
	for i := 1; i < len(ps)-1; i++ {
		b.WriteString(corner(ps[i-1], ps[i], ps[i+1], limit))
	}
	if len(ps) > 1 {
		b.WriteString(" L " + pair(ps[len(ps)-1]))
	}
	return b.String()
}
func corner(a, p, c geom.Point, limit int32) string {
	ux, uy, l1 := direction(a, p)
	vx, vy, l2 := direction(p, c)
	cross := ux*vy - uy*vx
	if cross == 0 || abs(ux)+abs(uy) != 1 || abs(vx)+abs(vy) != 1 {
		return " L " + pair(p)
	}
	radius := min(int64(limit), int64(512), min(l1, l2)/2)
	if radius <= 0 {
		return " L " + pair(p)
	}
	sweep := 0
	if cross > 0 {
		sweep = 1
	}
	return fmt.Sprintf(" L %s %s A %s %s 0 0 %d %s %s", number(int64(p.X)-radius*ux), number(int64(p.Y)-radius*uy), number(radius), number(radius), sweep, number(int64(p.X)+radius*vx), number(int64(p.Y)+radius*vy))
}
func pathData(cs []scene.Command) string {
	var b strings.Builder
	for i, c := range cs {
		if i > 0 {
			b.WriteByte(' ')
		}
		b.WriteString(command(c))
	}
	return b.String()
}
func command(c scene.Command) string {
	switch v := c.(type) {
	case *scene.MoveTo:
		return "M " + pair(v.P)
	case *scene.LineTo:
		return "L " + pair(v.P)
	case *scene.CubicTo:
		return "C " + pair(v.C1) + " " + pair(v.C2) + " " + pair(v.P)
	case *scene.ClosePath:
		return "Z"
	case *scene.ArcTo:
		return arc(v)
	}
	return ""
}
func floor(a, b int64) int64 {
	q, r := a/b, a%b
	if r < 0 {
		q--
	}
	return q
}
func arc(a *scene.ArcTo) string {
	angle := int32((int64(a.A0) + int64(a.Sweep)) % 65536)
	x := int64(a.CX) + floor(2*int64(a.R)*int64(geom.CosQ15(angle))+32768, 65536)
	y := int64(a.CY) + floor(2*int64(a.R)*int64(geom.SinQ15(angle))+32768, 65536)
	large, sweep := 0, 0
	if abs(int64(a.Sweep)) > 32768 {
		large = 1
	}
	if a.Sweep > 0 {
		sweep = 1
	}
	return fmt.Sprintf("A %s %s 0 %d %d %s %s", number(int64(a.R)), number(int64(a.R)), large, sweep, number(x), number(y))
}
func (r *renderer) marker(m *scene.MarkerRef) (string, error) {
	for _, row := range gen.Markers {
		if row.Name != m.Marker {
			continue
		}
		if len(row.Points) < 2 {
			return "", &ConfigError{"marker lacks outline: " + m.Marker}
		}
		ps := make([]geom.Point, 0, len(row.Points))
		for _, p := range row.Points {
			point, err := markerPoint(p, row.Ref, m)
			if err != nil {
				return "", err
			}
			ps = append(ps, point)
		}
		style, tag := "mark", "polygon"
		switch row.Paint {
		case "hollow":
			style = "mark-hollow"
		case "open":
			style, tag = "edge", "polyline"
		}
		return r.markerParts(tag, style, ps, row.Breaks)
	}
	return "", &ConfigError{"unknown marker: " + m.Marker}
}
func markerPoint(p, ref [2]int32, m *scene.MarkerRef) (geom.Point, error) {
	x, y := int64(p[0])-int64(ref[0]), int64(p[1])-int64(ref[1])
	switch m.Axis {
	case scene.AxisMinusX:
		x, y = -x, -y
	case scene.AxisPlusY:
		x, y = -y, x
	case scene.AxisMinusY:
		x, y = y, -x
	}
	x += int64(m.At.X)
	y += int64(m.At.Y)
	if x < -2147483648 || x > 2147483647 || y < -2147483648 || y > 2147483647 {
		return geom.Point{}, geom.ErrOverflow
	}
	return geom.Point{X: int32(x), Y: int32(y)}, nil
}

func (r *renderer) markerParts(tag, style string, ps []geom.Point, breaks []uint32) (string, error) {
	var out strings.Builder
	start := 0
	for _, end := range breaks {
		text, err := r.element(tag, scene.Shape{Style: style}, "points='"+points(ps[start:int(end)])+"'")
		if err != nil {
			return "", err
		}
		out.WriteString(text)
		start = int(end)
	}
	text, err := r.element(tag, scene.Shape{Style: style}, "points='"+points(ps[start:])+"'")
	if err != nil {
		return "", err
	}
	out.WriteString(text)
	return out.String(), nil
}
func (r *renderer) text(t *scene.Text) (string, error) {
	if _, e := styleRow(t.Style); e != nil {
		return "", e
	}
	key := class(t.Style, t.Series)
	r.used[key] = true
	var b strings.Builder
	x := int64(t.Rect.X)
	switch t.Align {
	case scene.AlignMiddle:
		x += int64(t.Rect.W) / 2
	case scene.AlignEnd:
		x += int64(t.Rect.W)
	}
	fmt.Fprintf(&b, "<text class='emd-t-%s emd-s-%s' x='%s' font-size='%d' xml:space='preserve'", t.Role.String(), key, number(x), t.Size)
	if t.Align != scene.AlignStart {
		fmt.Fprintf(&b, " text-anchor='%s'", t.Align.String())
	}
	b.WriteByte('>')
	lh := int64(1280)
	if t.Role == scene.TextRoleTitle {
		lh = 1536
	}
	for k, line := range t.Lines {
		y := int64(t.Rect.Y) + int64(k)*lh + lh/2 + int64(t.Size)*64*35/100
		fmt.Fprintf(&b, "<tspan x='%s' y='%s'>", number(x), number(y))
		for _, run := range line {
			b.WriteString(runText(run))
		}
		b.WriteString("</tspan>")
	}
	b.WriteString("</text>\n")
	return b.String(), nil
}
func runText(run scene.Run) string {
	out := escape(run.Text)
	if run.Italic {
		out = "<tspan font-style='italic'>" + out + "</tspan>"
	}
	if run.Bold {
		out = "<tspan font-weight='600'>" + out + "</tspan>"
	}
	return out
}
