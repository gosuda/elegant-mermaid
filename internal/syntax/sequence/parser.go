package sequence

import (
	"slices"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

const (
	codeNesting      = "limit/nesting-depth"
	codeUnexpected   = "sequence/unexpected-token"
	codeUnknown      = "sequence/unknown-statement"
	codeUnterminated = "sequence/unterminated"

	maxDepth = 64
)

func Parse(src []byte, removed []source.Span) (*Start, []diag.Diagnostic) {
	text := string(src)
	cleaned := source.Clean(src, removed)
	p := &parser{src: text, cleaned: cleaned, tokens: lexCleaned(cleaned)}
	for p.kind() == "NEWLINE" {
		p.at++
	}
	header, ok := p.expect("SD")
	if !ok {
		header = Token{Kind: "SD"}
	}
	document := p.document(0, nil)
	if p.kind() == "UNTERMINATED" {
		token := p.take()
		p.unterminated(token.Text, token.Span.Start)
	}
	return &Start{Span: source.Span{Start: header.Span.Start, End: len(text)}, Header: header, Document: document}, p.diags
}

type parser struct {
	src     string
	cleaned *source.Cleaned
	tokens  []Token
	at      int
	diags   []diag.Diagnostic
}

func (p *parser) token() Token {
	if p.at < len(p.tokens) {
		return p.tokens[p.at]
	}
	return Token{Kind: "EOF", Span: source.Span{Start: len(p.src), End: len(p.src)}}
}

func (p *parser) kind() string {
	if p.at < len(p.tokens) {
		return p.tokens[p.at].Kind
	}
	return "EOF"
}

func (p *parser) take() Token {
	t := p.token()
	if p.at < len(p.tokens) {
		p.at++
	}
	return t
}

func (p *parser) raw(span source.Span) string {
	return string(p.cleaned.Slice(span))
}

func (p *parser) contentEnd() int {
	for i := min(p.at, len(p.tokens)) - 1; i >= 0; i-- {
		if p.tokens[i].Kind != "NEWLINE" {
			return p.tokens[i].Span.End
		}
	}
	return 0
}

func endOfLines(lines []Line, start int) int {
	end := start
	for _, line := range lines {
		end = max(end, line.Span.End)
	}
	return end
}

func (p *parser) issue(code, message string, span source.Span) {
	p.diags = append(p.diags, Diagnostic(code, message, span))
}

func Diagnostic(code, message string, span source.Span) diag.Diagnostic {
	return diag.Diagnostic{Code: code, Severity: diag.SeverityError, Message: message, Span: span, Help: diagnosticHelp(code)}
}

func diagnosticHelp(code string) string {
	for i := range gen.Diagnostics {
		if gen.Diagnostics[i].Code == code {
			return gen.Diagnostics[i].Help
		}
	}
	return ""
}

func (p *parser) unexpected(expected ...string) {
	token := p.token()
	names := slices.Clone(expected)
	slices.Sort(names)
	p.issue(codeUnexpected, "unexpected "+p.raw(token.Span)+", expected one of: "+strings.Join(names, ", "), token.Span)
}

func (p *parser) unterminated(opener string, start int) {
	if n := len(p.diags); n > 0 && (p.diags[n-1].Code == codeUnterminated || p.diags[n-1].Code == codeNesting) {
		return
	}
	p.issue(codeUnterminated, "unterminated "+opener, source.Span{Start: start, End: len(p.src)})
}

func (p *parser) unknownStatement() {
	first := p.token()
	end := max(p.lineEnd(), first.Span.Start)
	p.issue(codeUnknown, "unknown statement "+first.Text, source.Span{Start: first.Span.Start, End: end})
	p.skipLine()
}

func (p *parser) lineEnd() int {
	for i := p.at; i < len(p.tokens); i++ {
		switch p.tokens[i].Kind {
		case "NEWLINE", "EOF", "UNTERMINATED":
			return p.tokens[i].Span.Start
		}
	}
	return len(p.src)
}

func (p *parser) skipLine() {
	for {
		switch p.kind() {
		case "EOF", "UNTERMINATED":
			return
		case "NEWLINE":
			p.take()
			return
		}
		p.take()
	}
}

func (p *parser) expect(kind string) (Token, bool) {
	if p.kind() == kind {
		return p.take(), true
	}
	p.unexpected(kind)
	return Token{}, false
}

func (p *parser) finishLine(expected ...string) {
	switch p.kind() {
	case "NEWLINE":
		p.take()
	case "EOF", "UNTERMINATED":
	default:
		p.unexpected(expected...)
		p.skipLine()
	}
}

func (p *parser) document(depth int, stops []string) Document {
	if depth > maxDepth {
		token := p.token()
		p.issue(codeNesting, "nesting depth exceeds 64", token.Span)
		p.skipDepth(stops)
		return Document{Span: source.Span{Start: token.Span.Start, End: token.Span.Start}}
	}
	start := p.token().Span.Start
	var lines []Line
	for {
		kind := p.kind()
		if kind == "EOF" || kind == "UNTERMINATED" || slices.Contains(stops, kind) {
			break
		}
		if kind == "NEWLINE" || kind == "INVALID" {
			lines = append(lines, Line{Span: p.take().Span})
			continue
		}
		before := p.at
		if statement := p.statement(depth); statement != nil {
			lines = append(lines, Line{Span: statement.Span, Statement: statement})
		} else if p.at == before {
			p.unknownStatement()
		}
	}
	return Document{Span: source.Span{Start: start, End: endOfLines(lines, start)}, Lines: lines}
}

func (p *parser) skipDepth(stops []string) {
	for {
		kind := p.kind()
		if kind == "EOF" || kind == "UNTERMINATED" || slices.Contains(stops, kind) {
			return
		}
		p.take()
	}
}

func (p *parser) statement(depth int) *Statement {
	start := p.token().Span.Start
	built := p.statementKind(p.kind(), depth, start)
	if built == nil {
		return nil
	}
	return &Statement{Span: source.Span{Start: start, End: max(p.contentEnd(), start)}, Kind: built}
}

func (p *parser) statementKind(kind string, depth, start int) StatementKind {
	switch kind {
	case "participant", "actor_kw", "destroy", "create":
		return nonNil(p.participantStatement(kind))
	case "box":
		return nonNil(p.boxBlock(start))
	case "loop", "rect", "opt", "break", "alt", "par", "par_over", "critical":
		return nonNil(p.controlBlock(start, depth))
	case "ACTOR":
		return nonNil(p.signal())
	}
	return p.lineStatement(kind, start)
}

func nonNil[P interface {
	StatementKind
	comparable
}](node P) StatementKind {
	var zero P
	if node == zero {
		return nil
	}
	return node
}

func (p *parser) participantStatement(kind string) *ParticipantStatement {
	switch kind {
	case "participant":
		return p.participantPlain(nil, "")
	case "actor_kw":
		return p.participantPlain(nil, "actor")
	case "destroy":
		return p.destroyPlain(nil)
	}
	return p.created(p.take().Span)
}

func (p *parser) lineStatement(kind string, start int) StatementKind {
	switch kind {
	case "autonumber":
		return p.autonumber()
	case "activate":
		return p.activateStatement(start)
	case "deactivate":
		return p.deactivateStatement(start)
	case "note":
		return nonNil(p.noteStatement())
	case "links", "link", "properties", "details":
		return p.linkedStatement(kind)
	}
	return p.textStatement(kind, start)
}

func (p *parser) textStatement(kind string, start int) StatementKind {
	switch kind {
	case "title":
		return p.title(false)
	case "legacy_title":
		return p.title(true)
	case "acc_title":
		return p.accessibility(Accessibility{Title: true})
	case "acc_descr":
		return p.accessibility(Accessibility{})
	case "acc_multiline_value":
		return p.accessibilityBlock(start)
	}
	return nil
}

func (p *parser) created(create source.Span) *ParticipantStatement {
	switch p.kind() {
	case "participant":
		return p.participantPlain(&create, "")
	case "actor_kw":
		return p.participantPlain(&create, "actor")
	case "destroy":
		return p.destroyPlain(&create)
	}
	p.unexpected("actor_kw", "destroy", "participant")
	return nil
}

func (p *parser) participantPlain(create *source.Span, draw string) *ParticipantStatement {
	keyword := p.take().Span
	actor, ok := p.plainActor()
	if !ok {
		return nil
	}
	config, ok := p.configPart()
	if !ok {
		return nil
	}
	alias := p.aliasPart()
	p.finishLine("NEWLINE")
	p.checkQuotes(actor, alias)
	return &ParticipantStatement{Create: create, Keyword: keyword, Draw: draw, Actor: actor, Alias: alias, Config: config}
}

func (p *parser) destroyPlain(create *source.Span) *ParticipantStatement {
	keyword := p.take().Span
	actor, ok := p.plainActor()
	if !ok {
		return nil
	}
	p.finishLine("NEWLINE")
	return &ParticipantStatement{Create: create, Keyword: keyword, Destroy: true, Actor: actor}
}

func (p *parser) aliasPart() *Alias {
	if p.kind() != "AS" {
		return nil
	}
	token := p.take()
	text := p.take()
	return &Alias{Token: token, Text: Text2{Span: text.Span, Text: text.Text}}
}

func (p *parser) configPart() (*ConfigObject, bool) {
	if p.kind() != "CONFIG_START" {
		return nil, true
	}
	start := p.take()
	if p.kind() != "CONFIG_CONTENT" {
		p.rejectConfig("CONFIG_CONTENT")
		return nil, false
	}
	content := p.take()
	if p.kind() != "CONFIG_END" {
		p.rejectConfig("CONFIG_END")
		return nil, false
	}
	closer := p.take()
	return &ConfigObject{Span: source.Span{Start: start.Span.Start, End: closer.Span.End}, Content: content.Text, ContentSpan: content.Span}, true
}

func (p *parser) rejectConfig(expected string) {
	if p.kind() == "UNTERMINATED" {
		return
	}
	p.unexpected(expected)
	p.skipLine()
}

func (p *parser) plainActor() (Actor, bool) {
	if p.kind() != "ACTOR" {
		p.unexpected("ACTOR")
		p.skipLine()
		return Actor{}, false
	}
	token := p.take()
	return Actor{Span: token.Span, Text: token.Text}, true
}

func (p *parser) signal() *Signal {
	source, ok := p.plainActor()
	if !ok {
		return nil
	}
	centralStart := p.takeParens()
	if !isArrow(p.kind()) {
		p.unexpected("ARROW", "TXT")
		p.skipLine()
		return nil
	}
	arrow := p.take()
	suffix := p.suffixToken()
	centralEnd := suffix == nil && p.takeParens()
	target, ok := p.plainActor()
	if !ok {
		return nil
	}
	if p.kind() != "TXT" {
		p.unexpected("TXT")
		p.skipLine()
		return nil
	}
	text := p.take()
	return &Signal{
		Span:         spanOf(source.Span.Start, text.Span.End),
		Source:       source,
		CentralStart: centralStart,
		Arrow:        arrow,
		Suffix:       suffix,
		CentralEnd:   centralEnd,
		Target:       target,
		Text:         Text2{Span: text.Span, Text: text.Text},
	}
}

func (p *parser) takeParens() bool {
	if p.kind() != "()" {
		return false
	}
	p.take()
	return true
}

func (p *parser) suffixToken() *Token {
	if kind := p.kind(); kind != "+" && kind != "-" {
		return nil
	}
	t := p.take()
	return &t
}

func spanOf(start, end int) source.Span { return source.Span{Start: start, End: end} }

func (p *parser) autonumber() StatementKind {
	start := p.take().Span.Start
	node := &Autonumber{}
	switch p.kind() {
	case "NUM":
		first := p.take()
		node.Start = &first
		if p.kind() == "NUM" {
			second := p.take()
			node.Step = &second
		}
	case "off":
		token := p.take()
		node.Off = true
		node.OffSpan = token.Span
	}
	p.finishLine("NUM", "NEWLINE", "off")
	node.Span = spanOf(start, p.contentEnd())
	return node
}

func (p *parser) activateStatement(start int) StatementKind {
	keyword := p.take().Span
	actor, ok := p.plainActor()
	if !ok {
		return nil
	}
	p.finishLine("NEWLINE")
	return &Activate{Span: spanOf(start, p.contentEnd()), Keyword: keyword, Actor: actor}
}

func (p *parser) deactivateStatement(start int) StatementKind {
	keyword := p.take().Span
	actor, ok := p.plainActor()
	if !ok {
		return nil
	}
	p.finishLine("NEWLINE")
	return &Deactivate{Span: spanOf(start, p.contentEnd()), Keyword: keyword, Actor: actor}
}

func (p *parser) noteStatement() *NoteStatement {
	keyword := p.take().Span
	placementKind := p.kind()
	if placementKind != "over" && placementKind != "left_of" && placementKind != "right_of" {
		p.unexpected("left_of", "over", "right_of")
		p.skipLine()
		return nil
	}
	placement := p.take()
	actors, ok := p.noteActors(placementKind)
	if !ok {
		return nil
	}
	if p.kind() != "TXT" {
		p.unexpected("TXT")
		p.skipLine()
		return nil
	}
	text := p.take()
	p.finishLine("NEWLINE")
	return &NoteStatement{Span: spanOf(keyword.Start, text.Span.End), Placement: placement.Span, Over: placementKind == "over", Actors: actors, Text: Text2{Span: text.Span, Text: text.Text}}
}

func (p *parser) noteActors(placementKind string) ([]Actor, bool) {
	if placementKind == "over" {
		return p.noteOver()
	}
	actor, ok := p.plainActor()
	return []Actor{actor}, ok
}

func (p *parser) noteOver() ([]Actor, bool) {
	first, ok := p.plainActor()
	if !ok {
		return nil, false
	}
	actors := []Actor{first}
	if p.kind() == "," {
		p.take()
		second, ok := p.plainActor()
		if !ok {
			return nil, false
		}
		actors = append(actors, second)
	}
	return actors, true
}

func (p *parser) linkedStatement(kind string) StatementKind {
	keyword := p.take().Span
	actor, ok := p.plainActor()
	if !ok {
		return nil
	}
	if p.kind() != "TXT" {
		p.unexpected("TXT")
		p.skipLine()
		return nil
	}
	text := p.take()
	p.finishLine("NEWLINE")
	span := spanOf(keyword.Start, text.Span.End)
	body := Text2{Span: text.Span, Text: text.Text}
	switch kind {
	case "links":
		return &Links{Span: span, Keyword: keyword, Actor: actor, Text: body}
	case "link":
		return &Link{Span: span, Keyword: keyword, Actor: actor, Text: body}
	case "properties":
		return &Properties{Span: span, Keyword: keyword, Actor: actor, Text: body}
	}
	return &Details{Span: span, Keyword: keyword, Actor: actor, Text: body}
}

func (p *parser) title(legacy bool) StatementKind {
	token := p.take()
	skip := len("title ")
	if legacy {
		skip = len("title: ")
	}
	return &Title{Span: token.Span, Legacy: legacy, Value: sub(token.Text, skip, len(token.Text))}
}

func (p *parser) accessibility(node Accessibility) StatementKind {
	keyword := p.take().Span
	if p.kind() != "acc_value" {
		p.unexpected("acc_value")
		p.skipLine()
		return nil
	}
	value := p.take()
	node.Span, node.Value = spanOf(keyword.Start, value.Span.End), value.Span
	return &node
}

func (p *parser) accessibilityBlock(start int) StatementKind {
	value := p.take()
	return &Accessibility{Span: spanOf(start, value.Span.End), Value: value.Span}
}

func (p *parser) boxBlock(start int) *BoxBlock {
	keyword := p.take().Span
	text := p.take()
	if text.Kind != "restOfLine" {
		p.unexpected("restOfLine")
		return nil
	}
	section := p.boxSection()
	closer := p.take()
	if closer.Kind != "end" {
		p.unterminated("box", keyword.Start)
		p.skipDepth(nil)
		return nil
	}
	return &BoxBlock{Span: spanOf(start, closer.Span.End), Keyword: keyword, Text: Text2{Span: text.Span, Text: text.Text}, Section: section, Close: closer}
}

func (p *parser) boxSection() BoxSection {
	start := p.token().Span.Start
	var lines []Line
	for kind := p.kind(); kind != "EOF" && kind != "UNTERMINATED" && kind != "end"; kind = p.kind() {
		lines = p.boxLine(kind, lines)
	}
	return BoxSection{Span: spanOf(start, endOfLines(lines, start)), Lines: lines}
}

func (p *parser) boxLine(kind string, lines []Line) []Line {
	switch kind {
	case "NEWLINE":
		return append(lines, Line{Span: p.take().Span})
	case "INVALID":
		token := p.take()
		p.issue(codeUnexpected, "unexpected "+token.Text+", expected one of: NEWLINE, actor_kw, participant", token.Span)
		return lines
	}
	before, opened := p.at, p.token().Span.Start
	drawn := p.boxParticipant(kind)
	if drawn == nil {
		if p.at == before {
			p.unknownStatement()
		}
		return lines
	}
	span := spanOf(opened, max(p.contentEnd(), opened))
	return append(lines, Line{Span: span, Statement: &Statement{Span: span, Kind: drawn}})
}

func (p *parser) boxParticipant(kind string) *ParticipantStatement {
	switch kind {
	case "participant":
		return p.participantPlain(nil, "")
	case "actor_kw":
		return p.participantPlain(nil, "actor")
	case "destroy":
		return p.destroyPlain(nil)
	}
	return nil
}

func (p *parser) controlBlock(start, depth int) *ControlBlock {
	keyword := p.take()
	kind := controlKindName(keyword.Kind)
	text := p.take()
	if text.Kind != "restOfLine" {
		p.unexpected("restOfLine")
		return nil
	}
	separator := separatorFor(kind)
	stops := []string{"end"}
	if separator != "" {
		stops = []string{separator, "end"}
	}
	sections := []Section{{Title: Text2{Span: text.Span, Text: text.Text}, Document: p.document(depth+1, stops)}}
	for separator != "" && p.kind() == separator {
		token := p.take()
		head := p.take()
		if head.Kind != "restOfLine" {
			p.unexpected("restOfLine")
			return nil
		}
		sections = append(sections, Section{Separator: &token, Title: Text2{Span: head.Span, Text: head.Text}, Document: p.document(depth+1, stops)})
	}
	closer := p.take()
	if closer.Kind != "end" {
		p.unterminated(keyword.Kind, keyword.Span.Start)
		p.skipDepth(stops)
		return nil
	}
	return &ControlBlock{Span: spanOf(start, closer.Span.End), Keyword: keyword.Span, Kind: kind, Text: Text2{Span: text.Span, Text: text.Text}, Sections: sections, Close: closer}
}

func isArrow(kind string) bool {
	for _, rule := range arrows {
		if rule.kind == kind {
			return true
		}
	}
	return false
}

func controlKindName(kind string) string {
	switch kind {
	case "loop", "rect", "opt", "alt", "par", "par_over", "critical":
		return kind
	}
	return "break"
}

func separatorFor(kind string) string {
	switch kind {
	case "alt":
		return "else"
	case "par", "par_over":
		return "and"
	case "critical":
		return "option"
	}
	return ""
}
