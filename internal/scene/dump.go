package scene

import (
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type Stage uint8

const (
	StageLayout Stage = iota

	StageModel
)

func (s Stage) String() string {
	if s == StageModel {
		return "model"
	}
	return "layout"
}

type Limits struct {
	MaxNodes     int32
	MaxEdges     int32
	MaxTextBytes int32
}

func DefaultLimits() Limits {
	return Limits{MaxNodes: 2000, MaxEdges: 5000, MaxTextBytes: 1048576}
}

type Config struct {
	Key   string
	Value string
}

func ConfigString(key, value string) Config {
	return Config{Key: key, Value: string(diag.AppendString(nil, value))}
}

func ConfigInt(key string, value int32) Config {
	return Config{Key: key, Value: strconv.FormatInt(int64(value), 10)}
}

func ConfigBool(key string, value bool) Config {
	if value {
		return Config{Key: key, Value: "true"}
	}
	return Config{Key: key, Value: "false"}
}

type Options struct {
	Profile      Profile
	Thoroughness int32
	MaxWidth     int32
	Direction    Direction
	Limits       Limits
	Config       []Config
}

func DefaultOptions() Options {
	return Options{Thoroughness: 3, Direction: DirectionTB, Limits: DefaultLimits()}
}

type Dump struct {
	Stage   Stage
	Kind    string
	Options Options
	Canvas  geom.Size
	Boxes   []Box
	Routes  []Route
	Labels  []Label
	Regions [][]int
}

const (
	tagVersion  = `{"version":1,"stage":`
	tagKind     = `,"kind":`
	tagProfile  = `,"profile":`
	tagOptions  = `,"options":`
	tagCanvas   = `,"canvas":`
	tagBoxes    = `,"boxes":`
	tagRoutes   = `,"routes":`
	tagLabels   = `,"labels":`
	tagRegions  = `,"regions":`
	tagLimits   = `,"limits":`
	tagMaxNodes = `{"max_nodes":`
	newline     = "\n"
)

func (d *Dump) AppendJSON(dst []byte) []byte {
	dst = append(dst, tagVersion...)
	dst = diag.AppendString(dst, d.Stage.String())
	dst = append(dst, tagKind...)
	dst = diag.AppendString(dst, d.Kind)
	dst = append(dst, tagProfile...)
	dst = diag.AppendString(dst, d.Options.Profile.String())
	dst = append(dst, tagOptions...)
	dst = appendOptions(dst, d.Options)
	if d.Stage == StageLayout {
		dst = append(dst, tagCanvas...)
		dst = appendCanvas(dst, d.Canvas)
	}
	dst = append(dst, ',')
	dst = append(dst, newline...)
	dst = d.appendBoxes(dst)
	dst = append(dst, ',')
	dst = append(dst, newline...)
	dst = d.appendRoutes(dst)
	dst = append(dst, ',')
	dst = append(dst, newline...)
	dst = d.appendLabels(dst)
	if d.Stage == StageModel && len(d.Regions) > 0 {
		dst = append(dst, ',')
		dst = append(dst, newline...)
		dst = d.appendRegions(dst)
	}
	dst = append(dst, '}')
	return append(dst, newline...)
}

func appendOptions(dst []byte, o Options) []byte {
	dst = append(dst, '{')
	dst = append(dst, tagProfile[1:]...)
	dst = diag.AppendString(dst, o.Profile.String())
	dst = append(dst, `,"thoroughness":`...)
	dst = strconv.AppendInt(dst, int64(o.Thoroughness), 10)
	dst = append(dst, `,"max_width":`...)
	dst = strconv.AppendInt(dst, int64(o.MaxWidth), 10)
	dst = append(dst, `,"direction":`...)
	dst = diag.AppendString(dst, o.Direction.String())
	dst = append(dst, tagLimits...)
	dst = appendLimits(dst, o.Limits)
	for _, c := range o.Config {
		dst = append(dst, ',')
		dst = diag.AppendString(dst, c.Key)
		dst = append(dst, ':')
		dst = append(dst, c.Value...)
	}
	return append(dst, '}')
}

func appendLimits(dst []byte, l Limits) []byte {
	dst = append(dst, tagMaxNodes...)
	dst = strconv.AppendInt(dst, int64(l.MaxNodes), 10)
	dst = append(dst, `,"max_edges":`...)
	dst = strconv.AppendInt(dst, int64(l.MaxEdges), 10)
	dst = append(dst, `,"max_text_bytes":`...)
	dst = strconv.AppendInt(dst, int64(l.MaxTextBytes), 10)
	return append(dst, '}')
}

func appendCanvas(dst []byte, c geom.Size) []byte {
	dst = append(dst, `{"w":`...)
	dst = strconv.AppendInt(dst, int64(c.W), 10)
	dst = append(dst, `,"h":`...)
	dst = strconv.AppendInt(dst, int64(c.H), 10)
	return append(dst, '}')
}

func appendRect(dst []byte, r geom.Rect) []byte {
	dst = append(dst, `,"x":`...)
	dst = strconv.AppendInt(dst, int64(r.X), 10)
	dst = append(dst, `,"y":`...)
	dst = strconv.AppendInt(dst, int64(r.Y), 10)
	dst = append(dst, `,"w":`...)
	dst = strconv.AppendInt(dst, int64(r.W), 10)
	dst = append(dst, `,"h":`...)
	return strconv.AppendInt(dst, int64(r.H), 10)
}

func (d *Dump) appendBoxes(dst []byte) []byte {
	dst = append(dst, tagBoxes[1:]...)
	dst = append(dst, '[')
	for i, b := range d.Boxes {
		if i > 0 {
			dst = append(dst, ',')
			dst = append(dst, newline...)
		}
		dst = d.appendBox(dst, b)
	}
	return append(dst, ']')
}

func (d *Dump) appendBox(dst []byte, b Box) []byte {
	dst = append(dst, `{"id":`...)
	dst = diag.AppendString(dst, b.ID)
	dst = append(dst, `,"role":`...)
	dst = diag.AppendString(dst, b.Role.String())
	if d.Stage == StageLayout {
		dst = appendRect(dst, b.Rect)
	}
	dst = append(dst, `,"parent":`...)
	dst = diag.AppendString(dst, b.Parent)
	dst = append(dst, `,"exclusive":`...)
	dst = appendBool(dst, b.Exclusive)
	if d.Stage == StageModel {
		dst = d.appendModelBoxKeys(dst, b)
	}
	return append(dst, '}')
}

func (d *Dump) appendRoutes(dst []byte) []byte {
	dst = append(dst, tagRoutes[1:]...)
	dst = append(dst, '[')
	for i, r := range d.Routes {
		if i > 0 {
			dst = append(dst, ',')
			dst = append(dst, newline...)
		}
		dst = d.appendRoute(dst, r)
	}
	return append(dst, ']')
}

func (d *Dump) appendRoute(dst []byte, r Route) []byte {
	dst = append(dst, `{"id":`...)
	dst = diag.AppendString(dst, r.ID)
	dst = append(dst, `,"from":`...)
	dst = diag.AppendString(dst, r.From)
	dst = append(dst, `,"to":`...)
	dst = diag.AppendString(dst, r.To)
	dst = append(dst, `,"orthogonal":`...)
	dst = appendBool(dst, r.Orthogonal)
	if d.Stage == StageLayout {
		dst = append(dst, `,"points":`...)
		dst = appendPoints(dst, r.Points)
	} else {
		dst = appendModelRouteStyle(dst, r)
	}
	return append(dst, '}')
}

func (d *Dump) appendModelBoxKeys(dst []byte, b Box) []byte {
	if b.Role == RoleGroup || b.Direction != "" {
		dst = append(dst, `,"direction":`...)
		dst = diag.AppendString(dst, b.Direction)
	}
	if b.Shape != "" && b.Shape != "rect" && b.Shape != "squareRect" {
		dst = append(dst, `,"shape":`...)
		dst = diag.AppendString(dst, b.Shape)
	}
	if b.Icon {
		dst = append(dst, `,"icon":true`...)
	}
	if d.Kind == "architecture" || b.Text != "" {
		dst = append(dst, `,"text":`...)
		dst = diag.AppendString(dst, b.Text)
	}
	return dst
}

func appendModelRouteStyle(dst []byte, route Route) []byte {
	if route.MarkerStart != "" && route.MarkerStart != "none" {
		dst = append(dst, `,"marker_start":`...)
		dst = diag.AppendString(dst, route.MarkerStart)
	}
	if route.MarkerEnd != "" && route.MarkerEnd != "point" {
		dst = append(dst, `,"marker_end":`...)
		dst = diag.AppendString(dst, route.MarkerEnd)
	}
	if route.Stroke != "" && route.Stroke != "normal" {
		dst = append(dst, `,"stroke":`...)
		dst = diag.AppendString(dst, route.Stroke)
	}
	return appendModelRouteConstraints(dst, route)
}

func appendModelRouteConstraints(dst []byte, route Route) []byte {
	if route.FromSide != geom.SideNone {
		dst = append(dst, `,"from_side":`...)
		dst = diag.AppendString(dst, modelSideToken(route.FromSide))
	}
	if route.ToSide != geom.SideNone {
		dst = append(dst, `,"to_side":`...)
		dst = diag.AppendString(dst, modelSideToken(route.ToSide))
	}
	if route.MinLength > 1 {
		dst = append(dst, `,"min_length":`...)
		dst = strconv.AppendInt(dst, int64(route.MinLength), 10)
	}
	return dst
}

func modelSideToken(side geom.Side) string {
	return "TBLR"[side-1 : side]
}

func (d *Dump) appendLabels(dst []byte) []byte {
	dst = append(dst, tagLabels[1:]...)
	dst = append(dst, '[')
	for i, l := range d.Labels {
		if i > 0 {
			dst = append(dst, ',')
			dst = append(dst, newline...)
		}
		dst = d.appendLabel(dst, l)
	}
	return append(dst, ']')
}

func (d *Dump) appendRegions(dst []byte) []byte {
	dst = append(dst, tagRegions[1:]...)
	dst = append(dst, '[')
	for i, set := range d.Regions {
		if i > 0 {
			dst = append(dst, ',')
			dst = append(dst, newline...)
		}
		dst = append(dst, '[')
		for j, value := range set {
			if j > 0 {
				dst = append(dst, ',')
			}
			dst = strconv.AppendInt(dst, int64(value), 10)
		}
		dst = append(dst, ']')
	}
	return append(dst, ']')
}

func (d *Dump) appendLabel(dst []byte, l Label) []byte {
	dst = append(dst, `{"id":`...)
	dst = diag.AppendString(dst, l.ID)
	dst = append(dst, `,"owner":`...)
	dst = diag.AppendString(dst, l.Owner)
	dst = append(dst, `,"text":`...)
	dst = diag.AppendString(dst, l.Text)
	if d.Stage == StageLayout {
		dst = appendRect(dst, l.Rect)
	}
	dst = append(dst, `,"lines":`...)
	if d.Stage == StageLayout {
		dst = appendStrings(dst, l.Lines)
	} else {
		dst = append(dst, '[', ']')
	}
	return append(dst, '}')
}

func appendPoints(dst []byte, pts []geom.Point) []byte {
	dst = append(dst, '[')
	for i, p := range pts {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = append(dst, '[')
		dst = strconv.AppendInt(dst, int64(p.X), 10)
		dst = append(dst, ',')
		dst = strconv.AppendInt(dst, int64(p.Y), 10)
		dst = append(dst, ']')
	}
	return append(dst, ']')
}

func appendStrings(dst []byte, ss []string) []byte {
	dst = append(dst, '[')
	for i, s := range ss {
		if i > 0 {
			dst = append(dst, ',')
		}
		dst = diag.AppendString(dst, s)
	}
	return append(dst, ']')
}

func appendBool(dst []byte, v bool) []byte {
	if v {
		return append(dst, "true"...)
	}
	return append(dst, "false"...)
}
