package geom

import "testing"

func TestErrorTexts(t *testing.T) {
	if got := ErrOverflow.Error(); got != "arithmetic overflow" {
		t.Fatalf("overflow: %q", got)
	}
	if got := ErrDomain.Error(); got != "domain error" {
		t.Fatalf("domain: %q", got)
	}
}
