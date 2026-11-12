package measure

import "testing"

func TestFixedVectorWidths(t *testing.T) {
	for _, c := range []struct {
		text  string
		width int32
	}{{"", 0}, {"Start", 2086}, {"Choice", 3041}, {"yes", 1550}, {"日本語", 2688}} {
		got, err := RoleLabel.Width(c.text)
		if err != nil || got != c.width {
			t.Fatalf("%q: %d %v, want %d", c.text, got, err, c.width)
		}
		metric := ForRole(RoleLabel)
		metric.FontFamily = true
		scaled, err := metric.TextWidth(c.text)
		if err != nil || scaled != c.width*108/100 {
			t.Fatalf("font factor: %d %v", scaled, err)
		}
	}
}

func TestASCIIWidthOracle(t *testing.T) {
	for n := 1; n <= 50; n++ {
		text := string(rune(32+n)) + string(rune(90-n))
		want := int32((naiveAdvanceSum(text)*896 + 2047) / 2048)
		got, err := RoleLabel.Width(text)
		if err != nil || got != want {
			t.Fatalf("%q: %d %v want %d", text, got, err, want)
		}
	}
}
