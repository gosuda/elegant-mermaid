package layout

import (
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/icon"
	"github.com/gosuda/elegant-mermaid/internal/layout/layered"
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

type Input struct {
	Kind        string
	Profile     scene.Profile
	Direction   scene.Direction
	Options     scene.Options
	Boxes       []Box
	Routes      []Route
	Labels      []Label
	Groups      []Group
	ClassRows   [][][]string
	Sizes       []geom.Size
	Exact       []bool
	Attachments []layered.Attachment
	RegionSets  []layered.RegionSet
	IconPacks   []*icon.Pack
}

type Box struct {
	ID        string
	Role      scene.BoxRole
	Shape     string
	Icon      bool
	Parent    string
	Exclusive bool
	Direction string
	Text      string
}

type Route struct {
	ID          string
	From        string
	To          string
	Orthogonal  bool
	MarkerStart string
	MarkerEnd   string
	Line        string
	MinLength   int
	FromSide    geom.Side
	ToSide      geom.Side
}

type Label struct {
	ID    string
	Owner string
	Role  scene.TextRole
	Text  string
}

type Group struct {
	ID            string
	Parent        string
	DirectionSpan source.Span
}
