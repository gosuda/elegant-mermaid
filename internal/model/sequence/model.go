package sequence

import (
	"slices"
	"strconv"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
)

const (
	codeInactive        = "sequence/inactive-participant"
	codeBoxConflict     = "sequence/participant-box-conflict"
	codeCreateExists    = "sequence/create-existing-participant"
	codeCreatingMissing = "sequence/creating-message-missing"
	codeDestroyMissing  = "sequence/destroying-message-missing"

	None = -1
)

var honored = []string{
	"activationWidth", "actorMargin", "boxMargin", "boxTextMargin", "diagramMarginX", "diagramMarginY",
	"height", "labelBoxHeight", "labelBoxWidth", "look", "noteMargin", "theme", "width", "wrap", "wrapPadding",
}

var drawKinds = []string{"actor", "boundary", "collections", "control", "database", "entity", "queue"}

type Wrap uint8

const (
	WrapDefault Wrap = iota
	WrapOn
	WrapOff
)

type Pair struct {
	Key   string
	Value string
}

type Model struct {
	AccTitle          string
	AccDescr          string
	Title             string
	HasTitle          bool
	Actors            []Actor
	Events            []Event
	Boxes             []ParticipantBox
	Wrap              bool
	Config            []ConfigEntry
	Declarations      []ActorDeclaration
	ActivationHistory []Activation
}

type ActorDeclaration struct {
	ID   string
	Span source.Span
}

type Activation struct {
	Actor int
	Open  bool
	Span  source.Span
}

type DumpKind uint8

const (
	DumpBool DumpKind = iota
	DumpInteger
	DumpString
)

type DumpValue struct {
	Kind    DumpKind
	Bool    bool
	Integer int64
	String  string
}

type ConfigEntry struct {
	Key   string
	Value DumpValue
}

type Actor struct {
	ID          string
	Span        source.Span
	Label       string
	Kind        string
	Wrap        Wrap
	Created     bool
	CreatedAt   int
	DestroyedAt int
	BoxIndex    int
	Links       []Pair
	Properties  []Pair
}

type Event interface {
	event()
}

type Message struct {
	From, To     int
	Text         string
	Span         source.Span
	Dotted       bool
	Numbered     bool
	HeadStart    string
	HeadEnd      string
	CentralStart bool
	CentralEnd   bool
	Creates      bool
	Destroys     bool
	Wrap         Wrap
}

type Placement uint8

const (
	LeftOf Placement = iota
	RightOf
	Over
)

type Note struct {
	Placement Placement
	Actors    [2]int
	Text      string
	Span      source.Span
	Wrap      Wrap
}

type FragmentStart struct {
	Kind  string
	Title string
	Span  source.Span
	Wrap  Wrap
}

type FragmentElse struct {
	StartEvent int
	Title      string
	Span       source.Span
	Wrap       Wrap
}

type FragmentEnd struct {
	StartEvent int
}

type ActivateStart struct {
	Actor int
}

type ActivateEnd struct {
	Actor int
}

type ParticipantBox struct {
	Label    string
	Wrap     Wrap
	Color    string
	HasColor bool
	Span     source.Span
}

func (*Message) event()       {}
func (*Note) event()          {}
func (*FragmentStart) event() {}
func (*FragmentElse) event()  {}
func (*FragmentEnd) event()   {}
func (*ActivateStart) event() {}
func (*ActivateEnd) event()   {}

type resolver struct {
	src             string
	cleaned         *source.Cleaned
	model           *Model
	diags           []diag.Diagnostic
	indices         map[string]int
	activations     []int
	pendingCreate   int
	pendingDestroy  int
	autonumberStart int64
	autonumberStep  int64
	autonumberOn    bool
	messageCount    int64
	currentBox      int
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := newResolver(src)
	r.lines(document.Document.Lines)
	r.model.Config = sortedConfig(r.model.Config)
	return r.model, r.diags
}

func newResolver(src []byte) *resolver {
	pre := syntax.Preprocess(src)
	model := &Model{Wrap: pre.Wrap}
	var blocks []syntax.ConfigValue
	if pre.HasConfig {
		blocks = append(blocks, pre.Config)
	}
	if pre.HasInit {
		blocks = append(blocks, pre.Init)
	}
	for _, block := range blocks {
		readSequenceConfig(model, block)
	}
	return &resolver{
		src: string(src), cleaned: source.Clean(src, pre.Removed), model: model, indices: map[string]int{},
		pendingCreate: None, pendingDestroy: None,
		autonumberStart: 100, autonumberStep: 100, currentBox: None,
	}
}

func readSequenceConfig(model *Model, block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == "sequence" })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		if !slices.Contains(honored, field.Key) {
			continue
		}
		if field.Key == "wrap" && field.Value.Kind == syntax.ValueBool && field.Value.Bool {
			model.Wrap = true
		}
		if value, ok := dumpValue(field.Value); ok {
			model.Config = upsertConfig(model.Config, field.Key, value)
		}
	}
}

func upsertConfig(entries []ConfigEntry, key string, value DumpValue) []ConfigEntry {
	if i := slices.IndexFunc(entries, func(e ConfigEntry) bool { return e.Key == key }); i >= 0 {
		entries[i].Value = value
		return entries
	}
	return append(entries, ConfigEntry{Key: key, Value: value})
}

func sortedConfig(entries []ConfigEntry) []ConfigEntry {
	slices.SortFunc(entries, func(a, b ConfigEntry) int {
		switch {
		case a.Key < b.Key:
			return -1
		case a.Key > b.Key:
			return 1
		}
		return 0
	})
	return entries
}

func dumpValue(value syntax.ConfigValue) (DumpValue, bool) {
	switch value.Kind {
	case syntax.ValueBool:
		return DumpValue{Kind: DumpBool, Bool: value.Bool}, true
	case syntax.ValueInteger, syntax.ValueDecimal:
		n, err := strconv.ParseInt(value.Text, 10, 64)
		return DumpValue{Kind: DumpInteger, Integer: n}, err == nil
	case syntax.ValueString:
		return DumpValue{Kind: DumpString, String: value.Text}, true
	}
	return DumpValue{}, false
}

func plainValue(value syntax.ConfigValue) (string, bool) {
	switch value.Kind {
	case syntax.ValueString, syntax.ValueInteger, syntax.ValueDecimal:
		return value.Text, true
	case syntax.ValueBool:
		return strconv.FormatBool(value.Bool), true
	}
	return "", false
}
