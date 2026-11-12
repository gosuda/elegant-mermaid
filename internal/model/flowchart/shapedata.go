package flowchart

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax"
	syngrammar "github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
)

const (
	codeLinkStyleIDUnknown    = "flowchart/linkstyle-id-unknown"
	codeTypedShapeUnsupported = "flowchart/typed-shape-unsupported"
	codeMalformedConfig       = "config/malformed"
)

var keywordShapes = map[string]string{
	"squareRect":    "squareRect",
	"roundedRect":   "roundedRect",
	"stadium":       "stadium",
	"subroutine":    "subroutine",
	"cylinder":      "cylinder",
	"circle":        "circle",
	"doublecircle":  "doublecircle",
	"diamond":       "diamond",
	"hexagon":       "hexagon",
	"odd":           "odd",
	"trapezoid":     "trapezoid",
	"inv-trapezoid": "inv_trapezoid",
	"lean-right":    "lean_right",
	"lean-left":     "lean_left",
	"ellipse":       "ellipse",
}

func init() {
	for _, shape := range gen.Shapes {
		keywordShapes[shape.ID] = shape.ID
		for _, alias := range shape.Aliases {
			if _, taken := keywordShapes[alias]; !taken {
				keywordShapes[alias] = shape.ID
			}
		}
	}
}

func resolveShapeID(value string) (string, bool) {
	if strings.ContainsAny(value, "_ABCDEFGHIJKLMNOPQRSTUVWXYZ") {
		return "", false
	}
	id, ok := keywordShapes[value]
	return id, ok
}

type shapeBody struct {
	text  string
	srcAt []int
	first int
	last  int
}

func buildShapeBody(data *syngrammar.ShapeData) shapeBody {
	var sb strings.Builder
	body := shapeBody{first: data.Span.Start, last: data.Span.End}
	for _, tok := range data.Tokens {
		for i := range len(tok.Text) {
			body.srcAt = append(body.srcAt, tok.Span.Start+i)
		}
		sb.WriteString(tok.Text)
	}
	body.text = sb.String()
	if len(body.srcAt) > 0 {
		body.first = body.srcAt[0]
		body.last = body.srcAt[len(body.srcAt)-1] + 1
	}
	return body
}

func (b shapeBody) readerInput() ([]byte, []int) {
	wrap := !strings.ContainsAny(b.text, "\r\n")
	size := len(b.text) + 2
	if !wrap {
		size = len(b.text)
	}
	out := make([]byte, 0, size)
	at := make([]int, 0, size)
	if wrap {
		out = append(out, '{')
		at = append(at, b.first)
	}
	for i := range len(b.text) {
		out = append(out, b.text[i])
		at = append(at, b.srcAt[i])
	}
	if wrap {
		out = append(out, '}')
		at = append(at, b.last)
	}
	return out, at
}

func (r *resolver) shapeValues(data *syngrammar.ShapeData) (map[string]string, map[string]source.Span) {
	body := buildShapeBody(data)
	input, at := body.readerInput()
	value, diags := syn.ParseConfigYAML(input, 0, len(input))
	for _, d := range diags {
		mapped := d
		mapped.Span = body.sourceSpan(d.Span, at)
		r.diags = append(r.diags, mapped)
	}
	values := map[string]string{}
	spans := map[string]source.Span{}
	if value.Kind != syn.ValueMapping {
		return values, spans
	}
	for _, entry := range value.Entries {
		values[entry.Key] = configText(entry.Value)
		spans[entry.Key] = body.sourceSpan(entry.KeySpan, at)
	}
	return values, spans
}

func (b shapeBody) sourceSpan(span source.Span, at []int) source.Span {
	start := b.sourceOffset(span.Start, at)
	end := b.sourceOffset(span.End, at)
	if end < start {
		end = start
	}
	return source.Span{Start: start, End: end}
}

func (b shapeBody) sourceOffset(pos int, at []int) int {
	if len(at) == 0 {
		return b.first
	}
	if pos < 0 {
		pos = 0
	}
	if pos >= len(at) {
		return at[len(at)-1] + 1
	}
	return at[pos]
}

func configText(value syn.ConfigValue) string {
	switch value.Kind {
	case syn.ValueString, syn.ValueInteger, syn.ValueDecimal:
		return value.Text
	case syn.ValueBool:
		if value.Bool {
			return "true"
		}
		return "false"
	}
	return ""
}

func (r *resolver) applyShapeData(node *Node, data *syngrammar.ShapeData) {
	values, spans := r.shapeValues(data)
	if node.Attrs == nil {
		node.Attrs = map[string]string{}
	}
	for key, value := range values {
		node.Attrs[key] = value
	}
	if shape, ok := values["shape"]; ok {
		id, resolved := resolveShapeID(shape)
		if !resolved {
			r.diags = append(r.diags, plainDiag(codeTypedShapeUnsupported, spans["shape"]))
			r.model.TypedShapes = append(r.model.TypedShapes, TypedShape{Value: shape, Span: spans["shape"]})
		} else {
			node.Shape = id
		}
	}
	if label, ok := values["label"]; ok {
		node.Label = decodeEntities(label)
	}
	if img, ok := values["img"]; ok && img != "" {
		node.Shape = "imageSquare"
	}
	if _, ok := values["icon"]; ok {
		node.Shape = iconShape(values["form"])
	}
}

func iconShape(form string) string {
	switch form {
	case "circle":
		return "iconCircle"
	case "square":
		return "iconSquare"
	case "rounded":
		return "iconRounded"
	}
	return "icon"
}
