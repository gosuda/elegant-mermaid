package layout

import "github.com/gosuda/elegant-mermaid/internal/scene"

type Input struct {
	Kind      string
	Profile   scene.Profile
	Direction scene.Direction
	Options   scene.Options
	Boxes     []Box
	Routes    []Route
	Labels    []Label
	Groups    []Group
}

type Box struct {
	ID        string
	Role      scene.BoxRole
	Shape     string
	Parent    string
	Exclusive bool
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
}

type Label struct {
	ID    string
	Owner string
	Role  scene.TextRole
	Text  string
}

type Group struct {
	ID        string
	Parent    string
	Direction string
	Text      string
}
