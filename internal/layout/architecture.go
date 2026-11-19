package layout

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	archmodel "github.com/gosuda/elegant-mermaid/internal/model/architecture"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	archparser "github.com/gosuda/elegant-mermaid/internal/syntax/architecture"
)

const architectureKind = "architecture"

func (d *Diagram) resolveArchitecture() (parsed, resolved []diag.Diagnostic) {
	ast, parsed := archparser.Parse(d.Source, d.Preprocessing.Removed)
	d.architecture, resolved = archmodel.Resolve(d.Source, ast)
	d.AccTitle, d.AccDescr = d.architecture.AccTitle, d.architecture.AccDescr
	return parsed, resolved
}

func (d *Diagram) architectureInput(profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic, error) {
	input, diagnostics := FromArchitecture(d.architecture, profile, options)
	return input, diagnostics, nil
}

func FromArchitecture(m *archmodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	for _, entry := range m.Config {
		options.Config = append(options.Config, scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value, 10)})
	}
	options.Profile = profile
	in := Input{Kind: architectureKind, Profile: profile, Direction: scene.DirectionTB, Options: options}
	for _, g := range m.Groups {
		in.Boxes = append(in.Boxes, Box{ID: g.ID, Role: scene.RoleGroup, Shape: archShape("group", "icon", g.Icon), Parent: g.Parent, Text: g.Title})
	}
	aligns := alignmentSuffixes(m)
	for _, n := range m.Nodes {
		in.Boxes = append(in.Boxes, nodeBox(n, aligns[n.ID]))
	}
	ids := allocateRouteIDs(in.Boxes, len(m.Edges))
	for i, e := range m.Edges {
		route := Route{ID: ids[i], From: e.From, To: e.To, Orthogonal: true, Line: "normal", FromSide: archSide(e.FromSide), ToSide: archSide(e.ToSide)}
		if e.FromInto {
			route.MarkerStart = "point"
		}
		if e.ToInto {
			route.MarkerEnd = "point"
		}
		in.Routes = append(in.Routes, route)
		if e.Title != "" {
			in.Labels = append(in.Labels, Label{ID: ids[i] + ".label", Owner: ids[i], Role: scene.TextRoleLabel, Text: e.Title})
		}
	}
	return in, nil
}

func nodeBox(n archmodel.Node, align string) Box {
	box := Box{ID: n.ID, Role: scene.RoleNode, Parent: n.Parent, Exclusive: true, Text: n.Title}
	switch {
	case n.Junction:
		box.Shape = "junction"
	case n.IconText != "":
		box.Shape = archShape("service", "icontext", escapeShape(n.IconText))
	default:
		box.Shape = archShape("service", "icon", n.Icon)
	}
	box.Shape += align
	return box
}

func archShape(kind, key, value string) string {
	if value == "" {
		return kind
	}
	return kind + ";" + key + "=" + value
}

func alignmentSuffixes(m *archmodel.Model) map[string]string {
	out := map[string]string{}
	for i, a := range m.Alignments {
		axis := "r"
		if a.Direction == "column" {
			axis = "c"
		}
		for pos, id := range a.Members {
			out[id] += ";align=" + strconv.Itoa(i) + ":" + axis + ":" + strconv.Itoa(pos)
		}
	}
	return out
}

func archSide(letter string) geom.Side {
	switch letter {
	case "L":
		return geom.SideLeft
	case "R":
		return geom.SideRight
	case "T":
		return geom.SideTop
	}
	return geom.SideBottom
}

func escapeShape(text string) string {
	var out strings.Builder
	for i := range len(text) {
		c := text[i]
		if c == '%' || c == ';' || c == '=' || c < 0x20 || c == 0x7f {
			out.WriteString("%" + strings.ToUpper(strconv.FormatInt(int64(c)+0x100, 16)[1:]))
			continue
		}
		out.WriteByte(c)
	}
	return out.String()
}

func unescapeShape(text string) string {
	var out strings.Builder
	for i := 0; i < len(text); i++ {
		if text[i] == '%' && i+2 < len(text) {
			if v, err := strconv.ParseUint(text[i+1:i+3], 16, 8); err == nil {
				out.WriteByte(byte(v))
				i += 2
				continue
			}
		}
		out.WriteByte(text[i])
	}
	return out.String()
}

type archShapeSpec struct {
	Kind     string
	Icon     string
	IconText string
	Aligns   []archAlignMember
}

type archAlignMember struct {
	Set, Pos int
	Column   bool
}

func parseArchShape(shape string) archShapeSpec {
	fields := strings.Split(shape, ";")
	spec := archShapeSpec{Kind: fields[0]}
	for _, field := range fields[1:] {
		key, value, _ := strings.Cut(field, "=")
		switch key {
		case "icon":
			spec.Icon = value
		case "icontext":
			spec.IconText = unescapeShape(value)
		case "align":
			if member, ok := parseAlignMember(value); ok {
				spec.Aligns = append(spec.Aligns, member)
			}
		}
	}
	return spec
}

func parseAlignMember(value string) (archAlignMember, bool) {
	parts := strings.Split(value, ":")
	if len(parts) != 3 {
		return archAlignMember{}, false
	}
	set, errSet := strconv.Atoi(parts[0])
	pos, errPos := strconv.Atoi(parts[2])
	if errSet != nil || errPos != nil || set < 0 || pos < 0 {
		return archAlignMember{}, false
	}
	return archAlignMember{Set: set, Pos: pos, Column: parts[1] == "c"}, true
}
