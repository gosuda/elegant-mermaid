package layout

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	blockmodel "github.com/gosuda/elegant-mermaid/internal/model/block"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const blockKind = "block"

func FromBlock(m *blockmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	for _, entry := range m.Config {
		options.Config = append(options.Config, scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)})
	}
	options.Profile = profile
	in := Input{Kind: blockKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	in.Boxes = append(in.Boxes, blockBox(m.Root, ""))
	in.walkBlocks(m.Root)
	ids := allocateRouteIDs(in.Boxes, len(m.Edges))
	for i, e := range m.Edges {
		in.Routes = append(in.Routes, Route{ID: ids[i], From: e.Start, To: e.End, Orthogonal: true, MarkerStart: blockMarker(e.ArrowStart), MarkerEnd: blockMarker(e.ArrowEnd), Line: blockStroke(e)})
		if e.Label != "" {
			in.Labels = append(in.Labels, Label{ID: ids[i] + ".label", Owner: ids[i], Role: scene.TextRoleLabel, Text: e.Label})
		}
	}
	return in, nil
}

func (in *Input) walkBlocks(parent *blockmodel.Block) {
	for _, child := range parent.Children {
		in.Boxes = append(in.Boxes, blockBox(child, parent.ID))
		if child.Type == "composite" {
			in.walkBlocks(child)
		}
	}
}

func blockBox(b *blockmodel.Block, parent string) Box {
	switch b.Type {
	case "composite":
		return Box{ID: b.ID, Role: scene.RoleGroup, Shape: blockShape("composite", b), Parent: parent}
	case "space":
		return Box{ID: b.ID, Role: scene.RoleNode, Shape: "space", Parent: parent}
	}
	return Box{ID: b.ID, Role: scene.RoleNode, Shape: blockShape(blockShapeID(b.Type), b), Parent: parent, Exclusive: true, Text: b.Label}
}

func blockShapeID(typ string) string {
	switch typ {
	case "na", "square":
		return "rect"
	case "round":
		return "roundedRect"
	case "rect_left_inv_arrow":
		return "odd"
	}
	return typ
}

func blockShape(typ string, b *blockmodel.Block) string {
	var out strings.Builder
	out.WriteString(typ)
	if typ == "composite" && b.Columns != blockmodel.AutoColumns {
		out.WriteString(";columns=" + strconv.Itoa(int(b.Columns)))
	}
	if b.Span != 1 {
		out.WriteString(";span=" + strconv.Itoa(int(b.Span)))
	}
	if len(b.Directions) > 0 {
		out.WriteString(";directions=" + strings.Join(b.Directions, ","))
	}
	return out.String()
}

func blockMarker(arrow string) string {
	switch arrow {
	case "arrow_point":
		return "point"
	case "arrow_cross":
		return "cross"
	case "arrow_circle":
		return "circle"
	}
	return ""
}

func blockStroke(e blockmodel.Edge) string {
	switch {
	case e.Thickness == "thick":
		return "thick"
	case e.Pattern == "dotted":
		return "dotted"
	}
	return "normal"
}

type blockShapeSpec struct {
	Type       string
	Columns    int32
	Span       int32
	Directions []string
}

func parseBlockShape(shape string) blockShapeSpec {
	fields := strings.Split(shape, ";")
	spec := blockShapeSpec{Type: fields[0], Columns: blockmodel.AutoColumns, Span: 1}
	for _, field := range fields[1:] {
		key, value, _ := strings.Cut(field, "=")
		switch key {
		case "columns":
			spec.Columns = parseCount(value, spec.Columns)
		case "span":
			spec.Span = parseCount(value, spec.Span)
		case "directions":
			spec.Directions = strings.Split(value, ",")
		}
	}
	if spec.Type == "" {
		spec.Type = "rect"
	}
	return spec
}

func parseCount(text string, fallback int32) int32 {
	value, err := strconv.ParseInt(text, 10, 32)
	if err != nil {
		return fallback
	}
	return int32(value)
}
