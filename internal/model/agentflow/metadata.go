package agentflow

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax"
	synagentflow "github.com/gosuda/elegant-mermaid/internal/syntax/agentflow"
)

func joinTokens(tokens []synagentflow.Token) string {
	parts := make([]string, len(tokens))
	for i, t := range tokens {
		parts[i] = t.Text
	}
	return strings.TrimSpace(strings.Join(parts, ""))
}

func parseIndex(text string) int {
	value, err := strconv.Atoi(text)
	if err != nil || value < 0 {
		return -1
	}
	return value
}

func contains(values []string, value string) bool {
	for _, v := range values {
		if v == value {
			return true
		}
	}
	return false
}

func cutAt(s string, at int) string {
	if at < 0 || at >= len(s) {
		return ""
	}
	return s[at:]
}

func idText(id synagentflow.IdString) string {
	parts := make([]string, len(id.Tokens))
	for i, t := range id.Tokens {
		parts[i] = t.Text
	}
	return strings.TrimSpace(strings.Join(parts, ""))
}

func report(code, message string, span source.Span) diag.Diagnostic {
	d := synagentflow.Diagnostic(code, message, span)
	switch code {
	case "agentflow/shape-unsupported", "agentflow/containment-violation", "interaction/unsafe-url":
		d.Severity = diag.SeverityWarning
	case "interaction/callback-ignored":
		d.Severity = diag.SeverityInfo
	}
	return d
}

func truthy(value syn.ConfigValue) bool {
	switch value.Kind {
	case syn.ValueNull:
		return false
	case syn.ValueBool:
		return value.Bool
	case syn.ValueInteger, syn.ValueDecimal:
		mantissa, _, _ := strings.Cut(value.Text, "e")
		mantissa, _, _ = strings.Cut(mantissa, "E")
		for i := 0; i < len(mantissa); i++ {
			if mantissa[i] >= '1' && mantissa[i] <= '9' {
				return true
			}
		}
		return false
	default:
		return true
	}
}

func valueText(value syn.ConfigValue) string {
	switch value.Kind {
	case syn.ValueString, syn.ValueInteger, syn.ValueDecimal:
		return value.Text
	case syn.ValueBool:
		if value.Bool {
			return "true"
		}
		return "false"
	case syn.ValueNull:
		return ""
	default:
		return ""
	}
}

func metadataLabel(entries []syn.ConfigEntry) (string, bool) {
	for _, entry := range entries {
		if entry.Key == "label" && truthy(entry.Value) {
			return syn.DecodeEntities(strings.TrimSpace(valueText(entry.Value))), true
		}
	}
	return "", false
}

func mergeEntries(target []syn.ConfigEntry, entries []syn.ConfigEntry) []syn.ConfigEntry {
	for _, entry := range entries {
		if entry.Key == "__proto__" || entry.Key == "prototype" || entry.Key == "constructor" {
			continue
		}
		sanitizeMetadata(&entry.Value)
		replaced := false
		for i := range target {
			if target[i].Key == entry.Key {
				target[i] = entry
				replaced = true
				break
			}
		}
		if !replaced {
			target = append(target, entry)
		}
	}
	return target
}

func sanitizeMetadata(value *syn.ConfigValue) {
	switch value.Kind {
	case syn.ValueMapping:
		kept := value.Entries[:0]
		for _, entry := range value.Entries {
			if entry.Key == "__proto__" || entry.Key == "prototype" || entry.Key == "constructor" {
				continue
			}
			kept = append(kept, entry)
		}
		value.Entries = kept
		for i := range value.Entries {
			sanitizeMetadata(&value.Entries[i].Value)
		}
	case syn.ValueSequence:
		for i := range value.Items {
			sanitizeMetadata(&value.Items[i])
		}
	}
}

func (m *Model) reference(id string, entries []syn.ConfigEntry, styled *synagentflow.StyledVertex) bool {
	if g := m.groupIndex(id); g >= 0 {
		m.Groups[g].Appearance.Metadata = mergeEntries(m.Groups[g].Appearance.Metadata, entries)
		if label, ok := metadataLabel(entries); ok {
			m.Groups[g].Title = label
		}
		return true
	}
	if len(styled.Metadata) == 0 && styled.Class == nil {
		return false
	}
	if e := m.edgeIndex(id); e >= 0 {
		m.Edges[e].Appearance.Metadata = mergeEntries(m.Edges[e].Appearance.Metadata, entries)
		if label, ok := metadataLabel(entries); ok {
			m.Edges[e].Label = label
		}
		return true
	}
	return false
}

func (m *Model) edgeIndex(id string) int {
	for i := range m.Edges {
		if m.Edges[i].ID == id {
			return i
		}
	}
	return -1
}

func (m *Model) metadata(data []synagentflow.ShapeData) []syn.ConfigEntry {
	var entries []syn.ConfigEntry
	for i := range data {
		value, errorSpan := metadataEntries(&data[i])
		if errorSpan != nil {
			m.diagnostics = append(m.diagnostics, report("agentflow/metadata-malformed", "invalid metadata value", *errorSpan))
		}
		entries = mergeEntries(entries, value)
	}
	return entries
}

func (m *Model) nodeMetadata(index int, entries []syn.ConfigEntry, metadata []synagentflow.ShapeData) {
	shape := m.shapeFromMetadata(entries, metadata)
	if index >= len(m.Nodes) {
		return
	}
	node := &m.Nodes[index]
	if shape != "" {
		node.Shape = shape
	}
	if label, ok := metadataLabel(entries); ok {
		node.Label = label
	}
	for _, entry := range entries {
		if entry.Key == "labelType" {
			node.LabelKind = labelKindOf(valueText(entry.Value))
		}
	}
}

func labelKindOf(name string) synagentflow.TextKind {
	switch name {
	case "markdown":
		return synagentflow.TextMarkdown
	case "string":
		return synagentflow.TextString
	}
	return synagentflow.TextPlain
}

func (m *Model) shapeFromMetadata(entries []syn.ConfigEntry, metadata []synagentflow.ShapeData) string {
	for _, entry := range entries {
		if entry.Key == "shape" && truthy(entry.Value) {
			return m.shapeEntry(entry, metadata)
		}
	}
	return ""
}

func (m *Model) shapeEntry(entry syn.ConfigEntry, metadata []synagentflow.ShapeData) string {
	value := valueText(entry.Value)
	span := shapeSpan(entry, metadata)
	if entry.Value.Kind != syn.ValueString || strings.Contains(value, "_") || hasUpperASCII(value) {
		m.diagnostics = append(m.diagnostics, report("agentflow/shape-unknown", "unknown shape "+value, span))
		return "roundedRect"
	}
	return m.normalize(value, span)
}

func shapeSpan(entry syn.ConfigEntry, metadata []synagentflow.ShapeData) source.Span {
	for i := len(metadata) - 1; i >= 0; i-- {
		if strings.Contains(metadata[i].Value, "shape") {
			return metadataValueSpan(&metadata[i], "shape")
		}
	}
	return entry.KeySpan
}

func hasUpperASCII(value string) bool {
	for i := 0; i < len(value); i++ {
		if value[i] >= 'A' && value[i] <= 'Z' {
			return true
		}
	}
	return false
}

var shapeAliases = map[string]string{
	"task":       "roundedRect",
	"square":     "roundedRect",
	"squareRect": "roundedRect",
	"rect":       "roundedRect",
	"":           "roundedRect",
	"tool":       "subroutine",
	"input":      "lean-right",
	"lean_right": "lean-right",
	"decision":   "diamond",
	"refdoc":     "lin-doc",
	"action":     "hexagon",
	"round":      "roundedRect",
}

var supportedShapes = []string{
	"roundedRect", "subroutine", "subprocess", "subproc", "framed-rectangle",
	"lean-right", "diamond", "lin-doc", "lined-document", "hexagon", "hex",
	"connector", "collapsedGroup",
}

var removedShapes = []string{
	"doc", "stadium", "terminal", "circle", "trapezoid", "inv_trapezoid", "inv-trapezoid",
	"doublecircle", "double-circle", "typeDeclaration", "procs", "lean_left", "lean-left",
	"in-out", "cylinder", "ellipse", "odd", "tag-rect", "tagged-rectangle", "delay",
	"half-rounded-rectangle", "lin-rect", "lined-rectangle", "win-pane", "window-pane",
	"curv-trap", "curved-trapezoid",
}

func registeredShape(name string) bool {
	for i := range gen.Shapes {
		if gen.Shapes[i].ID == name || contains(gen.Shapes[i].Aliases, name) {
			return true
		}
	}
	return false
}

func (m *Model) normalize(shape string, span source.Span) string {
	normalized := shape
	if alias, ok := shapeAliases[shape]; ok {
		normalized = alias
	}
	if contains(supportedShapes, normalized) {
		return normalized
	}
	m.diagnostics = append(m.diagnostics, shapeDiagnostic(shape, normalized, span))
	return "roundedRect"
}

func shapeDiagnostic(shape, normalized string, span source.Span) diag.Diagnostic {
	switch {
	case contains(removedShapes, normalized):
		return report("agentflow/shape-removed", "shape "+normalized+" was removed; using roundedRect", span)
	case registeredShape(normalized):
		return report("agentflow/shape-unsupported", "shape "+normalized+" is not supported; using roundedRect", span)
	}
	return report("agentflow/shape-unknown", "unknown shape "+shape, span)
}

func metadataEntries(data *synagentflow.ShapeData) ([]syn.ConfigEntry, *source.Span) {
	normalized := data.NormalizedValue()
	inline := !strings.ContainsAny(normalized, "\r\n")
	input := normalized
	if inline {
		input = "{" + normalized + "}"
	}
	value, errors := syn.ParseConfigYAML([]byte(input), 0, len(input))
	if len(errors) > 0 && !inline {
		if retried, ok := withoutTrailingCommas(input); ok {
			value, errors = retried, nil
		}
	}
	if len(errors) > 0 {
		span := metadataError(data, &errors[0].Span, inline)
		return nil, &span
	}
	if value.Kind != syn.ValueMapping {
		return nil, nil
	}
	entries := value.Entries
	for i := range entries {
		entries[i].KeySpan = metadataKeySpan(data, entries[i].Key)
	}
	return entries, nil
}

func withoutTrailingCommas(input string) (syn.ConfigValue, bool) {
	var lines []string
	for line := range strings.SplitSeq(input, "\n") {
		if trimmed, ok := strings.CutSuffix(strings.TrimRight(line, " \t"), ","); ok {
			line = trimmed
		}
		lines = append(lines, line)
	}
	retry := strings.Join(lines, "\n")
	retried, failures := syn.ParseConfigYAML([]byte(retry), 0, len(retry))
	return retried, len(failures) == 0
}

func metadataKeySpan(data *synagentflow.ShapeData, key string) source.Span {
	start := data.Span.End
	if offset := strings.Index(data.Value, key); offset >= 0 {
		start = data.Span.Start + 2 + offset
	}
	return source.Span{
		Start: start,
		End:   max(start, min(start+len(key), data.Span.End)),
	}
}

func metadataError(data *synagentflow.ShapeData, span *source.Span, inline bool) source.Span {
	fallback := source.Span{Start: len(data.Value), End: len(data.Value)}
	if span == nil {
		span = &fallback
	}
	offset := data.Span.Start + 2
	startAdjust := 0
	endAdjust := 0
	if inline {
		startAdjust, endAdjust = 1, 1
	}
	start := min(offset+max(span.Start-startAdjust, 0), data.Span.End)
	end := min(offset+max(span.End-endAdjust, 0), data.Span.End)
	return source.Span{Start: start, End: end}
}

func metadataValueSpan(data *synagentflow.ShapeData, key string) source.Span {
	at := strings.Index(data.Value, key)
	if at < 0 {
		return data.Span
	}
	tailAfterKey := data.Value[at+len(key):]
	colon := strings.Index(tailAfterKey, ":")
	if colon < 0 {
		return data.Span
	}
	at = at + len(key) + colon + 1
	tail := cutAt(data.Value, at)
	value := strings.TrimLeft(tail, " \t")
	start := data.Span.Start + 2 + at + len(tail) - len(value)
	text := cutAt(value, metadataValueEnd(value))
	start = min(start, data.Span.End)
	return source.Span{
		Start: start,
		End:   min(start+len(strings.TrimRight(text, " \t")), data.Span.End),
	}
}

func metadataValueEnd(value string) int {
	if len(value) > 0 && (value[0] == '\'' || value[0] == '"') {
		if n := strings.IndexByte(value[1:], value[0]); n >= 0 {
			return n + 2
		}
		return len(value)
	}
	if n := strings.IndexAny(value, ",\r\n}"); n >= 0 {
		return n
	}
	return len(value)
}
