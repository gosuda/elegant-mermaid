package layout

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	sequencemodel "github.com/gosuda/elegant-mermaid/internal/model/sequence"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const (
	sequenceKind = "sequence"

	tagMessage       = 0
	tagNote          = 1
	tagFragmentStart = 2
	tagFragmentElse  = 3
	tagFragmentEnd   = 4
	tagActivateStart = 5
	tagActivateEnd   = 6
	tagMask          = 15

	flagCreates      = 1 << 10
	flagDestroys     = 1 << 11
	flagCentralStart = 1 << 12
	flagCentralEnd   = 1 << 13
	flagNumbered     = 64
	wrapOn           = 16
	wrapOff          = 32
	placementShift   = 8
	noDestroyed      = -1
)

var fragmentKinds = []string{"loop", "rect", "opt", "alt", "par", "par_over", "critical", "break"}

func FromSequence(m *sequencemodel.Model, profile scene.Profile, options scene.Options) (Input, []diag.Diagnostic) {
	options = resolveOptions(options)
	options.Config = nil
	for _, entry := range m.Config {
		options.Config = append(options.Config, sequenceConfig(entry))
	}
	options.Profile = profile
	author := &sequenceAuthor{
		model:         m,
		in:            Input{Kind: sequenceKind, Profile: profile, Direction: scene.DirectionTB, Options: options},
		used:          map[string]struct{}{},
		sectionTitles: map[int][]string{},
	}
	author.participantBoxes()
	author.actors()
	author.events()
	author.labels()
	return author.in, nil
}

func sequenceConfig(entry sequencemodel.ConfigEntry) scene.Config {
	switch entry.Value.Kind {
	case sequencemodel.DumpBool:
		return scene.ConfigBool(entry.Key, entry.Value.Bool)
	case sequencemodel.DumpInteger:
		return scene.Config{Key: entry.Key, Value: strconv.FormatInt(entry.Value.Integer, 10)}
	}
	return scene.ConfigString(entry.Key, entry.Value.String)
}

func wrapToken(wrap sequencemodel.Wrap) string {
	switch wrap {
	case sequencemodel.WrapOn:
		return "w"
	case sequencemodel.WrapOff:
		return "n"
	}
	return ""
}

func wrapBits(wrap sequencemodel.Wrap) int {
	switch wrap {
	case sequencemodel.WrapOn:
		return wrapOn
	case sequencemodel.WrapOff:
		return wrapOff
	}
	return 0
}

func fragmentKindCode(kind string) int {
	return max(slices.Index(fragmentKinds, kind), 0)
}

func isFragmentShape(shape string) bool {
	return slices.Contains(fragmentKinds, shape)
}

type sequenceAuthor struct {
	model            *sequencemodel.Model
	in               Input
	used             map[string]struct{}
	actorIDs         []string
	actorBoxes       []int
	slots            []int
	boxIDs           []string
	fragmentBoxes    []int
	fragmentsStarted int
	sectionTitles    map[int][]string
}

func (a *sequenceAuthor) unique(wanted string) string {
	candidate := wanted
	for ordinal := 1; ; ordinal++ {
		if _, taken := a.used[candidate]; !taken {
			a.used[candidate] = struct{}{}
			return candidate
		}
		candidate = wanted + "~" + strconv.Itoa(ordinal)
	}
}

func (a *sequenceAuthor) anchoredBox(actor sequencemodel.Actor) (int, bool) {
	if actor.CreatedAt == sequencemodel.None && actor.BoxIndex != sequencemodel.None && actor.BoxIndex < len(a.model.Boxes) {
		return actor.BoxIndex, true
	}
	return 0, false
}

func (a *sequenceAuthor) participantBoxes() {
	members := make([]bool, len(a.model.Boxes))
	for _, actor := range a.model.Actors {
		if box, ok := a.anchoredBox(actor); ok {
			members[box] = true
		}
	}
	for index, box := range a.model.Boxes {
		if !members[index] {
			a.boxIDs = append(a.boxIDs, "")
			continue
		}
		id := a.unique("box" + strconv.Itoa(index))
		a.boxIDs = append(a.boxIDs, id)
		a.in.Boxes = append(a.in.Boxes, Box{ID: id, Role: scene.RoleGroup, Text: box.Label, Direction: wrapToken(box.Wrap)})
	}
}

func (a *sequenceAuthor) lifelineOrder() []int {
	order := make([]int, 0, len(a.model.Actors))
	for index, actor := range a.model.Actors {
		at := len(order)
		if box, ok := a.anchoredBox(actor); ok {
			for position := len(order) - 1; position >= 0; position-- {
				if other, member := a.anchoredBox(a.model.Actors[order[position]]); member && other == box {
					at = position + 1
					break
				}
			}
		}
		order = slices.Insert(order, at, index)
	}
	return order
}

func (a *sequenceAuthor) actors() {
	a.actorIDs = make([]string, len(a.model.Actors))
	a.actorBoxes = make([]int, len(a.model.Actors))
	a.slots = make([]int, len(a.model.Actors))
	for slot, index := range a.lifelineOrder() {
		actor := a.model.Actors[index]
		parent := ""
		if box, member := a.anchoredBox(actor); member && box < len(a.boxIDs) {
			parent = a.boxIDs[box]
		}
		id := a.unique(actor.ID)
		a.actorIDs[index] = id
		a.actorBoxes[index] = len(a.in.Boxes)
		a.slots[index] = slot
		shape := ""
		if actor.Kind != "participant" {
			shape = actor.Kind
		}
		a.in.Boxes = append(a.in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: shape, Parent: parent, Exclusive: actor.CreatedAt == sequencemodel.None, Text: actor.Label, Direction: wrapToken(actor.Wrap)})
	}
}

func (a *sequenceAuthor) fragmentParent() string {
	if len(a.fragmentBoxes) == 0 {
		return ""
	}
	return a.in.Boxes[a.fragmentBoxes[len(a.fragmentBoxes)-1]].ID
}

func (a *sequenceAuthor) pushRegion(regions ...int) {
	a.in.RegionSets = append(a.in.RegionSets, layered.RegionSet{Parent: len(a.in.RegionSets), Regions: regions})
}

func (a *sequenceAuthor) events() {
	for index, event := range a.model.Events {
		switch event := event.(type) {
		case *sequencemodel.FragmentStart:
			a.fragmentStart(event)
		case *sequencemodel.FragmentElse:
			a.fragmentElse(event)
		case *sequencemodel.FragmentEnd:
			a.fragmentEnd()
		case *sequencemodel.Note:
			a.note(event)
		case *sequencemodel.ActivateStart:
			a.pushRegion(tagActivateStart, a.slots[event.Actor])
		case *sequencemodel.ActivateEnd:
			a.pushRegion(tagActivateEnd, a.slots[event.Actor])
		case *sequencemodel.Message:
			a.message(index, event)
		}
	}
}

func (a *sequenceAuthor) lastFragmentBox() int {
	if len(a.fragmentBoxes) == 0 {
		return 0
	}
	return a.fragmentBoxes[len(a.fragmentBoxes)-1]
}

func (a *sequenceAuthor) fragmentStart(start *sequencemodel.FragmentStart) {
	parent := a.fragmentParent()
	ordinal := a.fragmentsStarted
	a.fragmentsStarted++
	id := a.unique("f" + strconv.Itoa(ordinal))
	index := len(a.in.Boxes)
	a.in.Boxes = append(a.in.Boxes, Box{ID: id, Role: scene.RoleGroup, Shape: start.Kind, Parent: parent, Text: start.Title, Direction: wrapToken(start.Wrap)})
	a.fragmentBoxes = append(a.fragmentBoxes, index)
	a.pushRegion(tagFragmentStart|fragmentKindCode(start.Kind)<<6|wrapBits(start.Wrap), index)
}

func (a *sequenceAuthor) fragmentElse(branch *sequencemodel.FragmentElse) {
	boxIndex := a.lastFragmentBox()
	section := len(a.sectionTitles[boxIndex])
	a.sectionTitles[boxIndex] = append(a.sectionTitles[boxIndex], branch.Title)
	a.pushRegion(tagFragmentElse|wrapBits(branch.Wrap), boxIndex, section)
}

func (a *sequenceAuthor) fragmentEnd() {
	a.pushRegion(tagFragmentEnd, a.lastFragmentBox())
	if n := len(a.fragmentBoxes); n > 0 {
		a.fragmentBoxes = a.fragmentBoxes[:n-1]
	}
}

func (a *sequenceAuthor) note(note *sequencemodel.Note) {
	parent := a.fragmentParent()
	ordinal := 0
	for _, box := range a.in.Boxes {
		if box.Shape == "note" {
			ordinal++
		}
	}
	id := a.unique("note" + strconv.Itoa(ordinal))
	index := len(a.in.Boxes)
	a.in.Boxes = append(a.in.Boxes, Box{ID: id, Role: scene.RoleNode, Shape: "note", Parent: parent, Text: note.Text, Direction: wrapToken(note.Wrap)})
	a.pushRegion(tagNote|int(note.Placement)<<placementShift|wrapBits(note.Wrap), a.slots[note.Actors[0]], a.slots[note.Actors[1]], index)
}

func (a *sequenceAuthor) nextRouteID() string {
	ordinal := len(a.in.Routes)
	id := "e" + strconv.Itoa(ordinal)
	for {
		if _, taken := a.used[id]; !taken {
			break
		}
		ordinal++
		id = "e" + strconv.Itoa(ordinal)
	}
	a.used[id] = struct{}{}
	return id
}

func messageFlags(message *sequencemodel.Message) int {
	flags := wrapBits(message.Wrap)
	for _, flag := range []struct {
		set  bool
		bits int
	}{{message.Creates, flagCreates}, {message.Destroys, flagDestroys}, {message.CentralStart, flagCentralStart}, {message.CentralEnd, flagCentralEnd}, {message.Numbered, flagNumbered}} {
		if flag.set {
			flags |= flag.bits
		}
	}
	return flags
}

func (a *sequenceAuthor) destroyedActor(eventIndex int) int {
	destroyed := slices.IndexFunc(a.model.Actors, func(actor sequencemodel.Actor) bool { return actor.DestroyedAt == eventIndex })
	if destroyed < 0 {
		return noDestroyed
	}
	return a.slots[destroyed]
}

func (a *sequenceAuthor) message(eventIndex int, message *sequencemodel.Message) {
	from, to := a.actorIDs[message.From], a.actorIDs[message.To]
	routeIndex := len(a.in.Routes)
	id := a.nextRouteID()
	destroyed := noDestroyed
	if message.Destroys {
		destroyed = a.destroyedActor(eventIndex)
	}
	if boxIndex := a.actorBoxes[message.To]; message.Creates && boxIndex < len(a.in.Boxes) {
		a.in.Boxes[boxIndex].Parent = a.fragmentParent()
	}
	line := "normal"
	if message.Dotted {
		line = "dotted"
	}
	a.in.Routes = append(a.in.Routes, Route{ID: id, From: from, To: to, Orthogonal: true, MarkerStart: message.HeadStart, MarkerEnd: message.HeadEnd, Line: line})
	if message.Text != "" {
		a.in.Labels = append(a.in.Labels, Label{ID: id + ".label", Owner: id, Role: scene.TextRoleBody, Text: message.Text})
	}
	a.pushRegion(tagMessage|messageFlags(message), a.slots[message.From], a.slots[message.To], routeIndex, destroyed)
}

func (a *sequenceAuthor) labels() {
	for index, box := range a.in.Boxes {
		if label, ok := sequenceBoxLabel(box); ok {
			role := scene.TextRoleLabel
			if box.Shape == "note" {
				role = scene.TextRoleBody
			}
			a.in.Labels = append(a.in.Labels, Label{ID: box.ID + ".label", Owner: box.ID, Role: role, Text: label})
		}
		for position, title := range a.sectionTitles[index] {
			a.in.Labels = append(a.in.Labels, Label{ID: box.ID + ".s" + strconv.Itoa(position), Owner: box.ID, Role: scene.TextRoleLabel, Text: title})
		}
	}
}

func isSequenceActor(box Box) bool {
	return box.Role == scene.RoleNode && box.Shape != "note"
}

func sequenceBoxLabel(box Box) (string, bool) {
	if box.Role == scene.RoleGroup {
		switch {
		case box.Shape == "rect":
			return "", false
		case isFragmentShape(box.Shape):
			return "[" + box.Text + "]", true
		}
		return box.Text, true
	}
	if isSequenceActor(box) {
		return "", false
	}
	return box.Text, true
}
