package main

import "fmt"

func validateMarkerOutline(m markerInput) error {
	if len(m.Points) < 2 {
		return fmt.Errorf("marker %q lacks outline", m.Name)
	}
	start := uint32(0)
	for _, end := range m.Breaks {
		if end < start+2 || uint64(end) > uint64(len(m.Points)-2) {
			return fmt.Errorf("marker %q has invalid breaks", m.Name)
		}
		start = end
	}
	return nil
}
