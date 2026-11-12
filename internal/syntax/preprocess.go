package syntax

import (
	"cmp"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Directive struct {
	Name    string
	Span    source.Span
	Body    source.Span
	HasBody bool
	Wrap    bool
	Init    ConfigValue
	HasInit bool
}

type Preprocessed struct {
	BodyStart   int
	Frontmatter source.Span
	HasFront    bool
	Root        ConfigValue
	Config      ConfigValue
	HasConfig   bool
	Directives  []Directive
	Init        ConfigValue
	HasInit     bool
	Wrap        bool
	Removed     []source.Span
	Diags       []diag.Diagnostic
}

func Preprocess(src []byte) Preprocessed {
	p := Preprocessed{Root: emptyMappingAt(0), Init: emptyMappingAt(0)}
	p.readFrontmatter(src)
	p.readDirectives(src)
	p.readComments(src)
	p.Removed = mergeRemoved(p.Removed)
	diag.Sort(p.Diags)
	return p
}

func mergeRemoved(spans []source.Span) []source.Span {
	slices.SortFunc(spans, func(a, b source.Span) int {
		return cmp.Or(cmp.Compare(a.Start, b.Start), cmp.Compare(a.End, b.End))
	})
	out := make([]source.Span, 0, len(spans))
	for _, s := range spans {
		if n := len(out); n > 0 && s.Start <= out[n-1].End {
			if s.End > out[n-1].End {
				out[n-1].End = s.End
			}
			continue
		}
		out = append(out, s)
	}
	return out
}

type frontmatterBounds struct {
	openEnd    int
	closeStart int
	closeEnd   int
}

func (p *Preprocessed) readFrontmatter(src []byte) {
	fence, ok := frontmatterFence(src)
	if !ok {
		return
	}
	p.Frontmatter = source.Span{Start: 0, End: fence.closeEnd}
	p.HasFront = true
	p.BodyStart = fence.closeEnd
	p.Removed = append(p.Removed, p.Frontmatter)
	root, diags, ok := parseConfigYAML(src, fence.openEnd, fence.closeStart)
	p.Root = root
	p.Diags = append(p.Diags, diags...)
	if ok {
		p.readFrontmatterConfig(src, root)
	}
}

func (p *Preprocessed) readFrontmatterConfig(src []byte, root ConfigValue) {
	if root.Kind != ValueMapping {
		return
	}
	i := findEntry(root, "config")
	if i < 0 {
		return
	}
	value := root.Entries[i].Value
	if value.Kind != ValueMapping {
		p.Diags = append(p.Diags, configDiagnostic(codeMalformed, msgFrontmatterMap, p.valueTokenSpan(src, value)))
		return
	}
	p.Config = value
	p.HasConfig = true
}

func (p *Preprocessed) valueTokenSpan(src []byte, value ConfigValue) source.Span {
	return configTokenSpan(src, value.Span.Start, len(src), 0)
}

func frontmatterFence(src []byte) (frontmatterBounds, bool) {
	openEnd, openNext := splitLine(src, 0, len(src))
	if openEnd == len(src) || !isFenceLine(src, 0, openEnd) {
		return frontmatterBounds{}, false
	}
	for p := openNext; p < len(src); {
		closeStart, closeEnd := splitLine(src, p, len(src))
		if closeStart == len(src) || !isFenceLine(src, p, closeStart) {
			p = closeEnd
			continue
		}
		return frontmatterBounds{openEnd: openNext, closeStart: p, closeEnd: closeEnd}, true
	}
	return frontmatterBounds{}, false
}

func isFenceLine(src []byte, start, lineEnd int) bool {
	begin := skipLineSpaces(src, start, lineEnd)
	end := lineEnd
	for end > begin && (src[end-1] == ' ' || src[end-1] == '\t') {
		end--
	}
	if end-begin != 3 {
		return false
	}
	return src[begin] == '-' && src[begin+1] == '-' && src[begin+2] == '-'
}

func (p *Preprocessed) readDirectives(src []byte) {
	for pos := p.BodyStart; pos < len(src); {
		at := indexDirective(src, pos)
		if at < 0 {
			return
		}
		raw := scanDirective(src, at)
		p.Removed = append(p.Removed, source.Span{Start: raw.start, End: raw.end})
		p.applyDirective(src, raw)
		pos = raw.end
	}
}

func indexDirective(src []byte, from int) int {
	for i := from; i+2 < len(src); i++ {
		if src[i] == '%' && src[i+1] == '%' && src[i+2] == '{' {
			return i
		}
	}
	return -1
}

type rawDirective struct {
	start   int
	end     int
	name    string
	after   int
	hasBody bool
	closed  bool
}

func scanDirective(src []byte, at int) rawDirective {
	raw := rawDirective{start: at, end: len(src)}
	nameStart := skipDirectiveSpace(src, at+3)
	i := nameStart
	for i < len(src) && isNameByte(src[i]) {
		i++
	}
	raw.name = string(src[nameStart:i])
	raw.after = skipDirectiveSpace(src, i)
	closeAt := indexClose(src, i)
	if closeAt < 0 {
		return raw
	}
	raw.closed = true
	raw.end = closeAt + 3
	raw.hasBody = raw.after < closeAt && src[raw.after] == ':'
	return raw
}

func indexClose(src []byte, from int) int {
	for i := from; i+2 < len(src); i++ {
		if src[i] == '}' && src[i+1] == '%' && src[i+2] == '%' {
			return i
		}
	}
	return -1
}

func skipDirectiveSpace(src []byte, from int) int {
	i := from
	for i < len(src) && (src[i] == ' ' || src[i] == '\t') {
		i++
	}
	return i
}

func isKnownDirective(name string) bool {
	switch name {
	case "init", "initialize", "wrap":
		return true
	}
	return false
}

func (p *Preprocessed) applyDirective(src []byte, raw rawDirective) {
	if !isKnownDirective(raw.name) {
		return
	}
	origin := source.Span{Start: raw.start, End: raw.start + 3}
	if !raw.closed {
		p.Diags = append(p.Diags, configDiagnostic(codeMalformed, msgDirective, origin))
		return
	}
	d := Directive{Name: raw.name, Span: source.Span{Start: raw.start, End: raw.end}}
	if !p.applyDirectiveBody(src, raw, &d, origin) {
		return
	}
	p.Directives = append(p.Directives, d)
}

func (p *Preprocessed) applyDirectiveBody(src []byte, raw rawDirective, d *Directive, origin source.Span) bool {
	if !raw.hasBody {
		if raw.after != raw.end-3 {
			p.Diags = append(p.Diags, configDiagnostic(codeMalformed, msgDirective, origin))
			return false
		}
		p.applyBareDirective(d)
		return true
	}
	if raw.name == "wrap" {
		p.Diags = append(p.Diags, configDiagnostic(codeMalformed, msgWrapBody, origin))
		return false
	}
	d.HasBody = true
	d.Body = source.Span{Start: raw.after + 1, End: raw.end - 3}
	return p.applyInitBody(src, raw, d)
}

func (p *Preprocessed) applyBareDirective(d *Directive) {
	if d.Name != "wrap" {
		return
	}
	d.Wrap = true
	p.Wrap = true
}

func (p *Preprocessed) applyInitBody(src []byte, raw rawDirective, d *Directive) bool {
	bodyStart := raw.after + 1
	bodyEnd := raw.end - 3
	first := skipDirectiveSpace(src, bodyStart)
	if first >= bodyEnd {
		return true
	}
	if src[first] != '{' {
		span := configTokenSpan(src, first, bodyEnd, 0)
		p.Diags = append(p.Diags, configDiagnostic(codeMalformed, msgDirectiveBody, span))
		return false
	}
	value, diags, ok := parseConfigJSON(src, bodyStart, bodyEnd)
	p.Diags = append(p.Diags, diags...)
	if !ok || value.Kind != ValueMapping {
		return false
	}
	d.Init = value
	d.HasInit = true
	p.mergeInit(value)
	return true
}

func (p *Preprocessed) mergeInit(value ConfigValue) {
	if !p.HasInit {
		p.Init = value
		p.HasInit = true
		return
	}
	p.Init = mergeMappings(p.Init, value)
}

func mergeMappings(base, later ConfigValue) ConfigValue {
	out := ConfigValue{Kind: ValueMapping, Span: base.Span}
	out.Entries = append(out.Entries, base.Entries...)
	for _, entry := range later.Entries {
		mergeEntry(&out, entry)
	}
	if later.Span.End > out.Span.End {
		out.Span.End = later.Span.End
	}
	return out
}

func mergeEntry(out *ConfigValue, entry ConfigEntry) {
	i := findEntry(*out, entry.Key)
	if i < 0 {
		out.Entries = append(out.Entries, entry)
		return
	}
	if out.Entries[i].Value.Kind == ValueMapping && entry.Value.Kind == ValueMapping {
		out.Entries[i].Value = mergeMappings(out.Entries[i].Value, entry.Value)
		return
	}
	out.Entries[i].Value = entry.Value
}

func (p *Preprocessed) readComments(src []byte) {
	for pos := p.BodyStart; pos < len(src); {
		lineEnd, next := splitLine(src, pos, len(src))
		if p.isCommentLine(src, pos, lineEnd) {
			p.Removed = append(p.Removed, source.Span{Start: pos, End: next})
		}
		pos = next
	}
}

func (p *Preprocessed) isCommentLine(src []byte, start, lineEnd int) bool {
	i := skipLineSpaces(src, start, lineEnd)
	if lineEnd-i < 2 || src[i] != '%' || src[i+1] != '%' {
		return false
	}
	return i+2 >= lineEnd || src[i+2] != '{'
}
