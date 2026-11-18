package eventmodeling

import "github.com/gosuda/elegant-mermaid/internal/source"

type Token struct {
	Kind string
	Text string
	Span source.Span
}

type Value struct {
	Text string
	Span source.Span
}

type EventModel struct {
	Span          source.Span
	Header        Token
	ModelEntities []EmModelEntity
	Frames        []EmFrame
	DataEntities  []EmDataEntity
	NoteEntities  []EmNoteEntity
	GwtEntities   []EmGwt
}

type EmFrame interface {
	Fields() *FrameFields
}

type FrameFields struct {
	Span             source.Span
	Keyword          source.Span
	Name             Value
	ModelEntityType  Value
	EntityIdentifier Value
	SourceFrames     []Value
	DataReference    *Value
	DataType         *Value
	DataInlineValue  *Value
}

type EmTimeFrame struct{ FrameFields }

type EmResetFrame struct{ FrameFields }

func (f *EmTimeFrame) Fields() *FrameFields { return &f.FrameFields }

func (f *EmResetFrame) Fields() *FrameFields { return &f.FrameFields }

type EmModelEntity struct {
	Span    source.Span
	Keyword source.Span
	Name    Value
}

type EmDataEntity struct {
	Span           source.Span
	Keyword        source.Span
	Name           Value
	DataType       *Value
	DataBlockValue Value
}

type EmNoteEntity struct {
	Span           source.Span
	Keyword        source.Span
	SourceFrame    Value
	DataType       *Value
	DataBlockValue Value
}

type EmGwt struct {
	Span            source.Span
	Keyword         source.Span
	SourceFrame     Value
	GivenStatements []EmGwtStatement
	WhenStatements  []EmGwtStatement
	ThenStatements  []EmGwtStatement
}

type EmGwtStatement struct {
	Span             source.Span
	ModelEntityType  Value
	EntityIdentifier Value
}
