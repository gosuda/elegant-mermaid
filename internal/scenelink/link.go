package scenelink

import "github.com/gosuda/elegant-mermaid/internal/scene"

type Command struct {
	Op     uint8
	Points [3][2]int32
}

type Glyph struct {
	Rune     rune
	Advance  int32
	Commands []Command
}

type Font struct {
	UnitsPerEm int32
	Glyphs     []Glyph
}

type Outlines [2]Font

var (
	Scene       func(any) (scene.Scene, bool)
	NewScene    func(scene.Scene) any
	NewOutlines func(Outlines) any
	OutlinesOf  func(any) (Outlines, bool)
)
