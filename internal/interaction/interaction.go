// Package interaction validates static-output links against the schemes that
// SVG anchors may carry.
package interaction

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

type OwnerLink struct {
	Owner      string
	Role       scene.GroupRole
	URL        string
	Tooltip    string
	HasTooltip bool
}

var safeSchemes = [3]string{"http", "https", "mailto"}

// SafeURL trims ASCII whitespace from both ends of raw and accepts it only when
// the text before the first colon names an allowed scheme, compared ASCII
// case-insensitively. The returned URL keeps the case of its scheme.
func SafeURL(raw string) (string, bool) {
	url := strings.Trim(raw, "\t\n\v\f\r ")
	scheme, _, found := strings.Cut(url, ":")
	if !found {
		return "", false
	}
	for _, s := range safeSchemes {
		if asciiEqualFold(scheme, s) {
			return url, true
		}
	}
	return "", false
}

func asciiEqualFold(a, b string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range len(a) {
		if lowerASCII(a[i]) != lowerASCII(b[i]) {
			return false
		}
	}
	return true
}

func lowerASCII(c byte) byte {
	if 'A' <= c && c <= 'Z' {
		return c + 'a' - 'A'
	}
	return c
}
