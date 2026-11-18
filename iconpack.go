package mermaid

import (
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/icon"
)

// IconPack is a parsed Iconify JSON collection. It is immutable and safe for concurrent use.
type IconPack struct{ pack *icon.Pack }

// ParseIconPack parses Iconify JSON. Invalid UTF-8 and malformed documents wrap ErrBadIconPack.
func ParseIconPack(data []byte) (*IconPack, error) {
	pack, err := icon.Parse(data)
	if err != nil {
		if format, ok := err.(*icon.FormatError); ok {
			return nil, fmt.Errorf("%w: %s", ErrBadIconPack, format.Reason)
		}
		return nil, fmt.Errorf("%w: %v", ErrBadIconPack, err)
	}
	return &IconPack{pack: pack}, nil
}
