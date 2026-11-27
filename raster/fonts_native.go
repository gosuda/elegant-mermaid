//go:build !js || !wasm

package raster

import (
	"embed"

	"github.com/gosuda/elegant-mermaid/internal/scenelink"
)

//go:embed fonts/*.ttf
var fonts embed.FS

func fallbackFiles(weight int) []string {
	return scenelink.FallbackFiles(weight)
}
