package raster

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestErrorTexts(t *testing.T) {
	large := scene.Scene{Dump: scene.Dump{Canvas: geom.Size{W: 16385 * 64, H: 64}}}
	_, err := encodeScene(large, Options{Scale: 1})
	if err == nil || err.Error() != "image is too large: 16385x1 pixels" {
		t.Fatalf("too large: %v", err)
	}
	if got := (&RasterError{Kind: Encode, Message: "disk full"}).Error(); got != "PNG encoding failed: disk full" {
		t.Fatalf("encode: %q", got)
	}
}
