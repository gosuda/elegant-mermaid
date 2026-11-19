package wardley

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

type Metadata struct {
	Field string
	Value string
	Span  source.Span
}

type Wardley struct {
	Span           source.Span
	Header         Token
	Metadata       []Metadata
	Size           *Size
	Evolution      *Evolution
	Anchors        []Anchor
	Components     []Component
	Links          []Link
	Evolves        []Evolve
	Pipelines      []Pipeline
	Notes          []Note
	Annotations    []Annotations
	Annotation     []Annotation
	Accelerators   []Accelerator
	Deaccelerators []Deaccelerator
}

type Size struct {
	Span          source.Span
	Width, Height Value
}

type Evolution struct {
	Span   source.Span
	Stages []EvolutionStage
}

type EvolutionStage struct {
	Span       source.Span
	Name       Value
	Boundary   *Value
	SecondName *Value
}

type Anchor struct {
	Span       source.Span
	Name       Value
	Visibility Value
	Evolution  Value
}

type Component struct {
	Span       source.Span
	Name       Value
	Visibility Value
	Evolution  Value
	Label      *Label
	Decorator  *Decorator
	Inertia    bool
}

type Label struct {
	Span    source.Span
	NegX    bool
	OffsetX Value
	NegY    bool
	OffsetY Value
}

type Decorator struct {
	Span     source.Span
	Strategy Value
}

type Link struct {
	Span      source.Span
	From      Value
	FromPort  *Value
	Arrow     *Value
	To        Value
	ToPort    *Value
	LinkLabel *Value
}

type Evolve struct {
	Span      source.Span
	Component Value
	Target    Value
}

type Pipeline struct {
	Span       source.Span
	Parent     Value
	Components []PipelineComponent
}

type PipelineComponent struct {
	Span      source.Span
	Name      Value
	Evolution Value
	Label     *Label
}

type Note struct {
	Span       source.Span
	Text       Value
	Visibility Value
	Evolution  Value
}

type Annotations struct {
	Span source.Span
	X, Y Value
}

type Annotation struct {
	Span   source.Span
	Number Value
	X, Y   Value
	Text   Value
}

type Accelerator struct {
	Span source.Span
	Name Value
	X, Y Value
}

type Deaccelerator Accelerator
