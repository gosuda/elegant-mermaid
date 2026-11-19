package layout

import "strconv"

func allocateRouteIDs(boxes []Box, count int) []string {
	taken := make(map[string]struct{}, len(boxes))
	for _, box := range boxes {
		taken[box.ID] = struct{}{}
	}
	ids := make([]string, count)
	ordinal := 0
	for i := range ids {
		id := "e" + strconv.Itoa(ordinal)
		for routeIDTaken(taken, id) {
			ordinal++
			id = "e" + strconv.Itoa(ordinal)
		}
		ids[i] = id
		taken[id] = struct{}{}
		ordinal++
	}
	return ids
}

func routeIDTaken(taken map[string]struct{}, id string) bool { _, exists := taken[id]; return exists }
