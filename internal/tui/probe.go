package tui

func da1Complete(stream []byte) bool {
	for i := 0; i+3 < len(stream); i++ {
		if stream[i] != 27 || stream[i+1] != '[' || stream[i+2] != '?' {
			continue
		}
		for _, b := range stream[i+3:] {
			if b == 'c' {
				return true
			}
			if b != ';' && (b < '0' || b > '9') {
				break
			}
		}
	}
	return false
}
