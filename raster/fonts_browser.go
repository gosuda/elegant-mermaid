//go:build js && wasm

package raster

import "embed"

//go:embed fonts/Inter-Regular.ttf fonts/Inter-SemiBold.ttf
var fonts embed.FS

func fallbackFiles(int) []string {
	return nil
}
