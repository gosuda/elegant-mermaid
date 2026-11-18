package eventmodeling

import "unicode/utf16"

func unwrapPayload(raw, opener string) string {
	units := utf16.Encode([]rune(raw))
	body := substring(units, indexOf(units, utf16.Encode([]rune(opener)))+len(opener), len(units))
	trimmed := substring(body, 0, lastIndexOf(body, '}')-1)
	return string(utf16.Decode(trimmed))
}

func substring(units []uint16, from, to int) []uint16 {
	from, to = min(max(from, 0), len(units)), min(max(to, 0), len(units))
	if from > to {
		from, to = to, from
	}
	return units[from:to]
}

func indexOf(units, needle []uint16) int {
	for at := 0; at+len(needle) <= len(units); at++ {
		if equalUnits(units[at:at+len(needle)], needle) {
			return at
		}
	}
	return -1
}

func equalUnits(a, b []uint16) bool {
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func lastIndexOf(units []uint16, unit uint16) int {
	for at := len(units) - 1; at >= 0; at-- {
		if units[at] == unit {
			return at
		}
	}
	return -1
}
