package main

import "testing"

func TestMarkerOutlineBreaks(t *testing.T) {
	for _, c := range []struct {
		name   string
		points int
		breaks []uint32
		valid  bool
	}{
		{"empty", 0, nil, false},
		{"single", 1, nil, false},
		{"connected", 3, nil, true},
		{"cross", 4, []uint32{2}, true},
		{"short-first", 4, []uint32{1}, false},
		{"short-last", 4, []uint32{3}, false},
		{"outside", 4, []uint32{99}, false},
		{"unordered", 8, []uint32{4, 2}, false},
	} {
		t.Run(c.name, func(t *testing.T) {
			err := validateMarkerOutline(markerInput{Name: c.name, Points: make([][2]int32, c.points), Breaks: c.breaks})
			if (err == nil) != c.valid {
				t.Fatalf("valid=%v: %v", c.valid, err)
			}
		})
	}
}
