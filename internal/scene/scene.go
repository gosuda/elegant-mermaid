package scene

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
)

type Profile uint8

const (
	ProfileVector Profile = iota

	ProfileCell
)

func (p Profile) String() string {
	if p == ProfileCell {
		return "cell"
	}
	return "vector"
}

type Direction uint8

const (
	DirectionTB Direction = iota

	DirectionBT

	DirectionLR

	DirectionRL
)

func (d Direction) String() string {
	switch d {
	case DirectionBT:
		return "BT"
	case DirectionLR:
		return "LR"
	case DirectionRL:
		return "RL"
	}
	return "TB"
}

func ParseDirection(s string) (Direction, bool) {
	switch s {
	case "TB", "TD":
		return DirectionTB, true
	case "BT":
		return DirectionBT, true
	case "LR":
		return DirectionLR, true
	case "RL":
		return DirectionRL, true
	}
	return DirectionTB, false
}

type BoxRole uint8

const (
	RoleNode BoxRole = iota

	RoleGroup
)

func (r BoxRole) String() string {
	if r == RoleGroup {
		return "group"
	}
	return "node"
}

type GroupRole uint8

const (
	GroupRoleDecor GroupRole = iota

	GroupRoleGroup

	GroupRoleEdge

	GroupRoleNode
)

func (r GroupRole) String() string {
	switch r {
	case GroupRoleGroup:
		return "group"
	case GroupRoleEdge:
		return "edge"
	case GroupRoleNode:
		return "node"
	}
	return "decor"
}

type TextRole uint8

const (
	TextRoleTitle TextRole = iota

	TextRoleLabel

	TextRoleBody
)

func (r TextRole) String() string {
	switch r {
	case TextRoleLabel:
		return "label"
	case TextRoleBody:
		return "body"
	}
	return "title"
}

type Align uint8

const (
	AlignStart Align = iota

	AlignMiddle

	AlignEnd
)

func (a Align) String() string {
	switch a {
	case AlignMiddle:
		return "middle"
	case AlignEnd:
		return "end"
	}
	return "start"
}

type LineStyle uint8

const (
	LineSolid LineStyle = iota

	LineDashed

	LineDotted

	LineDouble
)

func (l LineStyle) String() string {
	switch l {
	case LineDashed:
		return "dashed"
	case LineDotted:
		return "dotted"
	case LineDouble:
		return "double"
	}
	return "solid"
}

type WidthKind uint8

const (
	WidthNormal WidthKind = iota

	WidthEmphasis

	WidthUnits
)

type Width struct {
	Kind  WidthKind
	Units int32
}

type Axis uint8

const (
	AxisPlusX Axis = iota

	AxisMinusX

	AxisPlusY

	AxisMinusY
)

func (a Axis) String() string {
	switch a {
	case AxisMinusX:
		return "-x"
	case AxisPlusY:
		return "+y"
	case AxisMinusY:
		return "-y"
	}
	return "+x"
}

type Box struct {
	ID        string
	Role      BoxRole
	Rect      geom.Rect
	Parent    string
	Exclusive bool
}

type Route struct {
	ID         string
	From       string
	To         string
	Orthogonal bool
	Points     []geom.Point
}

type Label struct {
	ID    string
	Owner string
	Text  string
	Rect  geom.Rect
	Lines []string
}

type Run struct {
	Text   string
	Bold   bool
	Italic bool
}

type Shape struct {
	Style  string
	Series uint8
	Width  Width
	Line   LineStyle
}

type Primitive interface {
	primitive()
}

type Rect struct {
	Shape
	Rect geom.Rect
}

type RoundRect struct {
	Shape
	Rect geom.Rect
	R    int32
}

type Ellipse struct {
	Shape
	CX, CY, RX, RY int32
}

type Polygon struct {
	Shape
	Points []geom.Point
}

type Polyline struct {
	Shape
	Corner int32
	Points []geom.Point
}

type Path struct {
	Shape
	Commands []Command
}

type Text struct {
	Rect   geom.Rect
	Role   TextRole
	Size   int32
	Align  Align
	Style  string
	Series uint8
	Lines  [][]Run
}

type MarkerRef struct {
	Marker string
	At     geom.Point
	Axis   Axis
}

type SymbolRef struct {
	Symbol string
	At     geom.Point
	Style  string
}

func (*Rect) primitive()      {}
func (*RoundRect) primitive() {}
func (*Ellipse) primitive()   {}
func (*Polygon) primitive()   {}
func (*Polyline) primitive()  {}
func (*Path) primitive()      {}
func (*Text) primitive()      {}
func (*MarkerRef) primitive() {}
func (*SymbolRef) primitive() {}

type Command interface {
	command()
}

type MoveTo struct {
	P geom.Point
}

type LineTo struct {
	P geom.Point
}

type CubicTo struct {
	C1, C2, P geom.Point
}

type ArcTo struct {
	CX, CY, R, A0, Sweep int32
}

type ClosePath struct{}

func (*MoveTo) command()    {}
func (*LineTo) command()    {}
func (*CubicTo) command()   {}
func (*ArcTo) command()     {}
func (*ClosePath) command() {}

type Group struct {
	Role  GroupRole
	Owner string
	Items []Primitive
}

type Scene struct {
	Dump
	Groups []*Group
}
