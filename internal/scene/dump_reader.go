package scene

import (
	"bytes"
	"strconv"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

type dumpValue = syntax.ConfigValue

var apostrophe, escapedApostrophe = []byte("'"), []byte(`\u0027`)

func ReadMetricDump(data []byte) (Dump, error) {
	if !utf8.Valid(data) {
		return Dump{}, malformedf("invalid UTF-8")
	}
	escaped := bytes.ReplaceAll(data, apostrophe, escapedApostrophe)
	root, diagnostics := syntax.ParseConfigJSON(escaped, 0, len(escaped))
	if len(diagnostics) != 0 {
		return Dump{}, malformedf("invalid JSON")
	}
	d, err := decodeDump(root)
	if err != nil {
		return Dump{}, err
	}
	if err = d.WellFormed(); err != nil {
		return Dump{}, err
	}
	return d, nil
}

func dumpMember(v dumpValue, key string) (dumpValue, error) {
	if v.Kind != syntax.ValueMapping {
		return dumpValue{}, malformedf("expected object")
	}
	for _, entry := range v.Entries {
		if entry.Key == key {
			return entry.Value, nil
		}
	}
	return dumpValue{}, malformedf("missing %s", key)
}

func dumpText(v dumpValue, key string) (string, error) {
	member, err := dumpMember(v, key)
	if err != nil {
		return "", err
	}
	return stringValue(member)
}

func stringValue(v dumpValue) (string, error) {
	if v.Kind != syntax.ValueString {
		return "", malformedf("expected string")
	}
	return v.Text, nil
}

func dumpBool(v dumpValue, key string) (bool, error) {
	member, err := dumpMember(v, key)
	if err != nil {
		return false, err
	}
	if member.Kind != syntax.ValueBool {
		return false, malformedf("expected boolean")
	}
	return member.Bool, nil
}

func dumpArray(v dumpValue, key string) ([]dumpValue, error) {
	member, err := dumpMember(v, key)
	if err != nil {
		return nil, err
	}
	return sequenceItems(member)
}

func sequenceItems(v dumpValue) ([]dumpValue, error) {
	if v.Kind != syntax.ValueSequence {
		return nil, malformedf("expected array")
	}
	return v.Items, nil
}

func integerValue(v dumpValue) (int32, error) {
	if v.Kind != syntax.ValueInteger {
		return 0, malformedf("expected integer")
	}
	n, err := strconv.ParseInt(v.Text, 10, 32)
	if err != nil {
		return 0, malformedf("invalid integer")
	}
	return int32(n), nil
}

func dumpInt(v dumpValue, key string) (int32, error) {
	member, err := dumpMember(v, key)
	if err != nil {
		return 0, err
	}
	return integerValue(member)
}

func dumpRect(v dumpValue) (geom.Rect, error) {
	var r geom.Rect
	for _, field := range []struct {
		key    string
		target *int32
	}{{"x", &r.X}, {"y", &r.Y}, {"w", &r.W}, {"h", &r.H}} {
		var err error
		if *field.target, err = dumpInt(v, field.key); err != nil {
			return geom.Rect{}, err
		}
	}
	return r, nil
}

func decodeDump(root dumpValue) (Dump, error) {
	d := Dump{Kind: "flowchart", Options: DefaultOptions()}
	var err error
	if err = decodeHeader(root); err != nil {
		return Dump{}, err
	}
	if d.Options.Direction, err = decodeDirection(root); err != nil {
		return Dump{}, err
	}
	if d.Boxes, err = decodeAll(root, "boxes", decodeBox); err != nil {
		return Dump{}, err
	}
	if d.Routes, err = decodeAll(root, "routes", decodeRoute); err != nil {
		return Dump{}, err
	}
	if d.Labels, err = decodeAll(root, "labels", decodeLabel); err != nil {
		return Dump{}, err
	}
	d.Canvas, err = decodeCanvas(root)
	return d, err
}

func decodeHeader(root dumpValue) error {
	version, err := dumpInt(root, "version")
	if err != nil {
		return err
	}
	if version != 1 {
		return malformedf("expected version 1 layout dump")
	}
	stage, err := dumpText(root, "stage")
	if err != nil {
		return err
	}
	if stage != "layout" {
		return malformedf("expected version 1 layout dump")
	}
	profile, err := dumpText(root, "profile")
	if err != nil {
		return err
	}
	if profile != "vector" {
		return malformedf("--metrics needs --profile vector")
	}
	return nil
}

func decodeDirection(root dumpValue) (Direction, error) {
	options, err := dumpMember(root, "options")
	if err != nil {
		return DirectionTB, err
	}
	name, err := dumpText(options, "direction")
	if err != nil {
		return DirectionTB, err
	}
	switch name {
	case "TB", "BT", "LR", "RL":
		direction, _ := ParseDirection(name)
		return direction, nil
	}
	return DirectionTB, malformedf("invalid direction")
}

func decodeCanvas(root dumpValue) (geom.Size, error) {
	canvas, err := dumpMember(root, "canvas")
	if err != nil {
		return geom.Size{}, err
	}
	var size geom.Size
	if size.W, err = dumpInt(canvas, "w"); err != nil {
		return geom.Size{}, err
	}
	size.H, err = dumpInt(canvas, "h")
	return size, err
}

func decodeAll[T any](root dumpValue, key string, decode func(dumpValue) (T, error)) ([]T, error) {
	items, err := dumpArray(root, key)
	if err != nil {
		return nil, err
	}
	var out []T
	for _, item := range items {
		decoded, err := decode(item)
		if err != nil {
			return nil, err
		}
		out = append(out, decoded)
	}
	return out, nil
}

func decodeBox(v dumpValue) (Box, error) {
	var b Box
	var err error
	if b.ID, err = dumpText(v, "id"); err != nil {
		return b, err
	}
	role, err := dumpText(v, "role")
	if err != nil {
		return b, err
	}
	switch role {
	case "node":
		b.Role = RoleNode
	case "group":
		b.Role = RoleGroup
	default:
		return b, malformedf("invalid box role")
	}
	if b.Rect, err = dumpRect(v); err != nil {
		return b, err
	}
	if b.Parent, err = dumpText(v, "parent"); err != nil {
		return b, err
	}
	b.Exclusive, err = dumpBool(v, "exclusive")
	return b, err
}

func decodeRoute(v dumpValue) (Route, error) {
	var r Route
	var err error
	if r.ID, err = dumpText(v, "id"); err != nil {
		return r, err
	}
	if r.From, err = dumpText(v, "from"); err != nil {
		return r, err
	}
	if r.To, err = dumpText(v, "to"); err != nil {
		return r, err
	}
	if r.Orthogonal, err = dumpBool(v, "orthogonal"); err != nil {
		return r, err
	}
	r.Points, err = decodeAll(v, "points", decodePoint)
	return r, err
}

func decodePoint(v dumpValue) (geom.Point, error) {
	items, err := sequenceItems(v)
	if err != nil {
		return geom.Point{}, err
	}
	if len(items) != 2 {
		return geom.Point{}, malformedf("expected point")
	}
	x, err := integerValue(items[0])
	if err != nil {
		return geom.Point{}, err
	}
	y, err := integerValue(items[1])
	return geom.Point{X: x, Y: y}, err
}

func decodeLabel(v dumpValue) (Label, error) {
	var l Label
	var err error
	if l.ID, err = dumpText(v, "id"); err != nil {
		return l, err
	}
	if l.Owner, err = dumpText(v, "owner"); err != nil {
		return l, err
	}
	if l.Text, err = dumpText(v, "text"); err != nil {
		return l, err
	}
	if l.Rect, err = dumpRect(v); err != nil {
		return l, err
	}
	items, err := dumpArray(v, "lines")
	if err != nil {
		return l, err
	}
	for _, item := range items {
		line, err := stringValue(item)
		if err != nil {
			return l, err
		}
		l.Lines = append(l.Lines, line)
	}
	return l, nil
}
