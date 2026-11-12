package layered

import (
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func ValidateOwners(boxes []scene.Box, routes []scene.Route) error {
	ids := make(map[string]struct{}, len(boxes))
	for _, box := range boxes {
		ids[box.ID] = struct{}{}
	}
	for _, route := range routes {
		if _, ambiguous := ids[route.ID]; ambiguous {
			return fmt.Errorf("ambiguous box and route owner %q: %w", route.ID, ErrGraph)
		}
	}
	return nil
}
