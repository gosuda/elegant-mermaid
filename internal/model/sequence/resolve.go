package sequence

import (
	"slices"
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
)

func (r *resolver) issue(code, message string, span source.Span) {
	r.diags = append(r.diags, syn.Diagnostic(code, message, span))
}

func (r *resolver) lines(lines []syn.Line) {
	for _, line := range lines {
		if line.Statement != nil {
			r.statement(line.Statement)
		}
	}
}

func (r *resolver) statement(statement *syn.Statement) {
	switch node := statement.Kind.(type) {
	case *syn.ParticipantStatement:
		r.participant(node)
	case *syn.Signal:
		r.signal(node)
	case *syn.Autonumber:
		r.autonumber(node)
	case *syn.Activate:
		r.activate(node.Actor)
	case *syn.Deactivate:
		r.deactivate(node.Actor)
	case *syn.NoteStatement:
		r.note(node)
	case *syn.Title:
		r.title(node)
	case *syn.Accessibility:
		r.accessibility(node)
	default:
		r.linkedStatement(statement.Kind)
	}
}

func (r *resolver) linkedStatement(kind syn.StatementKind) {
	switch node := kind.(type) {
	case *syn.Links:
		r.linked(node.Actor, node.Text, linkedLinks)
	case *syn.Link:
		r.linked(node.Actor, node.Text, linkedLink)
	case *syn.Properties:
		r.linked(node.Actor, node.Text, linkedProperties)
	case *syn.Details:
		r.linked(node.Actor, node.Text, linkedDetails)
	case *syn.BoxBlock:
		r.boxBlock(node)
	case *syn.ControlBlock:
		r.control(node)
	}
}

func (r *resolver) accessibility(node *syn.Accessibility) {
	text := strings.TrimSpace(string(r.cleaned.Slice(node.Value)))
	if node.Title {
		r.model.AccTitle = text
		return
	}
	r.model.AccDescr = text
}

func (r *resolver) title(node *syn.Title) {
	value := node.Value
	if node.Legacy {
		value = strings.TrimLeft(value, " ")
	}
	r.model.Title, r.model.HasTitle = syntax.DecodeEntities(value), true
}

func sub(text string, from, to int) string {
	if from < 0 || to < from || to > len(text) {
		return ""
	}
	return text[from:to]
}

func (r *resolver) participant(participant *syn.ParticipantStatement) {
	actor := participant.Actor
	if _, exists := r.indices[actor.Text]; participant.Create != nil && exists {
		r.issue(codeCreateExists, "cannot create existing participant "+actor.Text, actor.Span)
		return
	}
	if participant.Destroy && participant.Create == nil {
		r.pendingDestroy = r.absentActor(actor)
		return
	}
	alias, hasAlias := "", participant.Alias != nil
	if hasAlias {
		alias = stripWrap(participant.Alias.Text.Text)
	}
	var metadata []Pair
	if participant.Config != nil {
		metadata = r.metadata(participant.Config)
	}
	distinctAlias := hasAlias && strings.TrimSpace(alias) != actor.Text
	index := r.definedActor(actor, alias, hasAlias, participantKind(participant.Draw, metadata), textOverride(alias))
	record := &r.model.Actors[index]
	if participant.Create != nil {
		record.Created = true
		r.pendingCreate = index
	}
	record.Links, record.Properties = nil, nil
	record.applyMetadata(metadata, distinctAlias)
	r.assignBox(index, actor)
}

func (a *Actor) applyMetadata(metadata []Pair, distinctAlias bool) {
	for _, field := range metadata {
		switch {
		case field.Key == "alias" && !distinctAlias && field.Value != "":
			a.Label = syntax.DecodeEntities(field.Value)
		case field.Key == "type":
		default:
			a.Properties = append(a.Properties, field)
		}
	}
}

func participantKind(draw string, metadata []Pair) string {
	for _, field := range metadata {
		if field.Key != "type" {
			continue
		}
		if slices.Contains(drawKinds, field.Value) {
			return field.Value
		}
		return "participant"
	}
	if draw == "actor" {
		return "actor"
	}
	return "participant"
}

func (r *resolver) assignBox(index int, actor syn.Actor) {
	if r.currentBox == None {
		return
	}
	record := &r.model.Actors[index]
	switch {
	case record.BoxIndex == None:
		record.BoxIndex = r.currentBox
	case record.BoxIndex != r.currentBox:
		r.issue(codeBoxConflict, "participant "+record.ID+" belongs to more than one box", actor.Span)
	}
}

func (r *resolver) definedActor(actor syn.Actor, alias string, hasAlias bool, kind string, wrap Wrap) int {
	r.model.Declarations = append(r.model.Declarations, ActorDeclaration{ID: actor.Text, Span: actor.Span})
	label := actor.Text
	if hasAlias {
		label = alias
	}
	if index, ok := r.indices[actor.Text]; ok {
		record := &r.model.Actors[index]
		if !record.Created {
			record.Label, record.Kind, record.Wrap = syntax.DecodeEntities(label), kind, wrap
		}
		return index
	}
	return r.addActor(Actor{ID: actor.Text, Span: actor.Span, Label: syntax.DecodeEntities(label), Kind: kind, Wrap: wrap})
}

func (r *resolver) absentActor(actor syn.Actor) int {
	if index, ok := r.indices[actor.Text]; ok {
		return index
	}
	return r.addActor(Actor{ID: actor.Text, Span: actor.Span, Label: syntax.DecodeEntities(actor.Text), Kind: "participant"})
}

func (r *resolver) addActor(actor Actor) int {
	index := len(r.model.Actors)
	actor.CreatedAt, actor.DestroyedAt, actor.BoxIndex = None, None, r.currentBox
	r.model.Actors = append(r.model.Actors, actor)
	r.activations = append(r.activations, 0)
	r.indices[actor.ID] = index
	return index
}

func (r *resolver) signal(signal *syn.Signal) {
	from, to := r.absentActor(signal.Source), r.absentActor(signal.Target)
	text, wrap := labelText(signal.Text.Text)
	headStart, headEnd := heads(signal.Arrow.Kind)
	if signal.Suffix != nil && signal.Suffix.Kind == "-" && r.activations[from] == 0 {
		r.issue(codeInactive, "participant "+r.model.Actors[from].ID+" is not active", signal.Suffix.Span)
	}
	creates := r.takePendingCreate(signal, to)
	destroyed := None
	if !creates {
		destroyed = r.takePendingDestroy(signal, from, to)
	}
	numbered := r.autonumberOn
	label := text
	if numbered {
		number := r.autonumberStart + r.messageCount*r.autonumberStep
		label = "(" + formatNumber(number) + ") " + text
	}
	event := len(r.model.Events)
	r.model.Events = append(r.model.Events, &Message{
		From: from, To: to, Text: label, Span: signal.Span, Dotted: dottedArrow(signal.Arrow.Kind), Numbered: numbered,
		HeadStart: headStart, HeadEnd: headEnd, CentralStart: signal.CentralStart, CentralEnd: signal.CentralEnd,
		Creates: creates, Destroys: destroyed != None, Wrap: wrap,
	})
	r.messageCount++
	if creates {
		r.model.Actors[to].CreatedAt = event
	}
	if destroyed != None {
		r.model.Actors[destroyed].DestroyedAt = event
	}
	r.applySuffix(signal.Suffix, from, to)
}

func (r *resolver) applySuffix(suffix *syn.Token, from, to int) {
	if suffix != nil {
		actor := from
		if suffix.Kind == "+" {
			actor = to
		}
		r.model.ActivationHistory = append(r.model.ActivationHistory, Activation{Actor: actor, Open: suffix.Kind == "+", Span: suffix.Span})
	}
	switch {
	case suffix == nil:
	case suffix.Kind == "+":
		r.activations[to]++
		r.model.Events = append(r.model.Events, &ActivateStart{Actor: to})
	case r.activations[from] > 0:
		r.activations[from]--
		r.model.Events = append(r.model.Events, &ActivateEnd{Actor: from})
	}
}

func (r *resolver) takePendingCreate(signal *syn.Signal, to int) bool {
	created := r.pendingCreate
	if created == None {
		return false
	}
	r.pendingCreate = None
	if created == to {
		return true
	}
	r.issue(codeCreatingMissing, "next message must target created participant "+r.model.Actors[created].ID, signal.Target.Span)
	return false
}

func (r *resolver) takePendingDestroy(signal *syn.Signal, from, to int) int {
	destroyed := r.pendingDestroy
	if destroyed == None {
		return None
	}
	r.pendingDestroy = None
	if destroyed != from && destroyed != to {
		r.issue(codeDestroyMissing, "next message must involve destroyed participant "+r.model.Actors[destroyed].ID, signal.Span)
		return None
	}
	return destroyed
}

func (r *resolver) autonumber(node *syn.Autonumber) {
	if node.Off {
		r.autonumberOn = false
		return
	}
	r.autonumberOn = true
	if node.Start != nil {
		if value, ok := hundredths(node.Start.Text); ok && value != 0 {
			r.autonumberStart = value
		}
	}
	if node.Step != nil {
		if value, ok := hundredths(node.Step.Text); ok && value != 0 {
			r.autonumberStep = value
		}
	}
}

func (r *resolver) activate(actor syn.Actor) {
	r.model.ActivationHistory = append(r.model.ActivationHistory, Activation{Actor: r.absentActor(actor), Open: true, Span: actor.Span})
	index := r.absentActor(actor)
	r.activations[index]++
	r.model.Events = append(r.model.Events, &ActivateStart{Actor: index})
}

func (r *resolver) deactivate(actor syn.Actor) {
	r.model.ActivationHistory = append(r.model.ActivationHistory, Activation{Actor: r.absentActor(actor), Span: actor.Span})
	index := r.absentActor(actor)
	if r.activations[index] == 0 {
		r.issue(codeInactive, "participant "+r.model.Actors[index].ID+" is not active", actor.Span)
		return
	}
	r.activations[index]--
	r.model.Events = append(r.model.Events, &ActivateEnd{Actor: index})
}

func (r *resolver) note(node *syn.NoteStatement) {
	placement := Over
	switch text := asciiLower(sub(r.src, node.Placement.Start, node.Placement.End)); {
	case strings.HasPrefix(text, "right"):
		placement = RightOf
	case strings.HasPrefix(text, "left"):
		placement = LeftOf
	}
	first := r.absentActor(node.Actors[0])
	second := first
	if len(node.Actors) > 1 {
		second = r.absentActor(node.Actors[1])
	}
	text, wrap := labelText(node.Text.Text)
	if node.Over {
		placement = Over
	}
	r.model.Events = append(r.model.Events, &Note{Placement: placement, Actors: [2]int{first, second}, Text: text, Span: node.Span, Wrap: wrap})
}

type linkedTarget uint8

const (
	linkedLinks linkedTarget = iota
	linkedLink
	linkedProperties
	linkedDetails
)

func (r *resolver) linked(actor syn.Actor, text syn.Text2, target linkedTarget) {
	index := r.absentActor(actor)
	raw := strings.TrimSpace(stripWrap(strings.TrimPrefix(text.Text, ":")))
	record := &r.model.Actors[index]
	switch target {
	case linkedLink:
		label, url := splitLink(raw)
		record.Links = upsert(record.Links, label, url)
	case linkedLinks:
		record.Links = mergePairs(record.Links, jsonMapping(raw))
	case linkedProperties:
		record.Properties = mergePairs(record.Properties, jsonMapping(raw))
	case linkedDetails:
		for _, member := range jsonMapping(raw) {
			if member.Value.Kind != syntax.ValueMapping {
				continue
			}
			switch member.Key {
			case "properties":
				record.Properties = mergePairs(record.Properties, member.Value.Entries)
			case "links":
				record.Links = mergePairs(record.Links, member.Value.Entries)
			}
		}
	}
}

func jsonMapping(text string) []syntax.ConfigEntry {
	parsed, _ := syntax.ParseConfigJSON([]byte(text), 0, len(text))
	return mappingEntries(parsed)
}

func mergePairs(fields []Pair, entries []syntax.ConfigEntry) []Pair {
	for _, entry := range entries {
		if value, ok := plainValue(entry.Value); ok {
			fields = upsert(fields, entry.Key, value)
		}
	}
	return fields
}

func (r *resolver) boxBlock(block *syn.BoxBlock) {
	raw := strings.TrimSpace(stripWrap(block.Text.Text))
	color, label, hasColor := boxColorLabel(raw)
	index := len(r.model.Boxes)
	r.model.Boxes = append(r.model.Boxes, ParticipantBox{Label: syntax.DecodeEntities(label), Wrap: textOverride(raw), Color: color, HasColor: hasColor, Span: block.Keyword})
	r.currentBox = index
	r.lines(block.Section.Lines)
	r.currentBox = None
}

func (r *resolver) control(block *syn.ControlBlock) {
	var title string
	wrap := WrapDefault
	if block.Kind == "rect" {
		title = syntax.DecodeEntities(strings.TrimSpace(block.Text.Text))
	} else {
		title, wrap = labelText(block.Text.Text)
	}
	event := len(r.model.Events)
	r.model.Events = append(r.model.Events, &FragmentStart{Kind: block.Kind, Title: title, Span: block.Keyword, Wrap: wrap})
	for _, section := range block.Sections {
		if section.Separator != nil {
			sectionTitle, sectionWrap := labelText(section.Title.Text)
			r.model.Events = append(r.model.Events, &FragmentElse{StartEvent: event, Title: sectionTitle, Span: section.Separator.Span, Wrap: sectionWrap})
		}
		r.lines(section.Document.Lines)
	}
	r.model.Events = append(r.model.Events, &FragmentEnd{StartEvent: event})
}

type metadataBody struct {
	text        []byte
	start       int
	wrapped     bool
	open, close int
}

func newMetadataBody(config *syn.ConfigObject) metadataBody {
	trimmed := strings.TrimSpace(config.Content)
	body := metadataBody{start: config.ContentSpan.Start + strings.Index(config.Content, trimmed)}
	if strings.ContainsAny(trimmed, "\r\n") {
		body.text = []byte(trimmed)
		return body
	}
	body.text = []byte("{" + trimmed + "}")
	body.wrapped = true
	body.open, body.close = config.Span.Start+1, config.Span.End-1
	return body
}

func (b metadataBody) offset(at int) int {
	if !b.wrapped {
		return b.start + min(max(at, 0), len(b.text))
	}
	inner := len(b.text) - 2
	switch {
	case at <= 0:
		return b.open
	case at <= inner:
		return b.start + at - 1
	case at == inner+1:
		return b.close
	}
	return b.close + 1
}

func (r *resolver) metadata(config *syn.ConfigObject) []Pair {
	body := newMetadataBody(config)
	value, diags := syntax.ParseConfigYAML(body.text, 0, len(body.text))
	for _, d := range diags {
		d.Span = source.Span{Start: body.offset(d.Span.Start), End: body.offset(d.Span.End)}
		r.diags = append(r.diags, d)
	}
	return mergePairs(nil, mappingEntries(value))
}

func mappingEntries(value syntax.ConfigValue) []syntax.ConfigEntry {
	if value.Kind != syntax.ValueMapping {
		return nil
	}
	return value.Entries
}

func upsert(fields []Pair, key, value string) []Pair {
	if i := slices.IndexFunc(fields, func(p Pair) bool { return p.Key == key }); i >= 0 {
		fields[i].Value = value
		return fields
	}
	return append(fields, Pair{Key: key, Value: value})
}

func hundredths(text string) (int64, bool) {
	text = strings.TrimSpace(text)
	whole, fraction, _ := strings.Cut(text, ".")
	if whole == "" && fraction == "" {
		return 0, false
	}
	n, err := strconv.ParseInt(whole, 10, 64)
	if err != nil || n > (1<<63-1)/100 || n < -(1<<63)/100 {
		return 0, false
	}
	value, scale := n*100, int64(10)
	for i := 0; i < len(fraction) && i < 2; i++ {
		digit := fraction[i]
		if digit < '0' || digit > '9' {
			return 0, false
		}
		value += int64(digit-'0') * scale
		scale /= 10
	}
	return value, true
}

func formatNumber(hundredths int64) string {
	whole, fraction := hundredths/100, hundredths%100
	switch {
	case fraction == 0:
		return strconv.FormatInt(whole, 10)
	case fraction%10 == 0:
		return strconv.FormatInt(whole, 10) + "." + strconv.FormatInt(fraction/10, 10)
	}
	return strconv.FormatInt(whole, 10) + "." + strconv.FormatInt(fraction, 10)
}
