package mermaid

import (
	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/scenelink"
)

func init() {
	scenelink.Scene = func(value any) (scene.Scene, bool) {
		s, ok := value.(*Scene)
		if !ok || s == nil {
			return scene.Scene{}, false
		}
		return s.value, true
	}
	scenelink.NewScene = func(value scene.Scene) any {
		return &Scene{value: value}
	}
	scenelink.NewOutlines = func(fonts scenelink.Outlines) any {
		return &GlyphOutlines{fonts: fonts}
	}
	scenelink.OutlinesOf = func(value any) (scenelink.Outlines, bool) {
		outlines, ok := value.(*GlyphOutlines)
		if !ok || outlines == nil {
			return scenelink.Outlines{}, false
		}
		return outlines.fonts, true
	}
}
