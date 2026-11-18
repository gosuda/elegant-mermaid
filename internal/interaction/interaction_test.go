package interaction

import "testing"

func TestSafeURL(t *testing.T) {
	for _, c := range []struct {
		raw  string
		want string
	}{
		{" \t\r\n\v\fHtTp://example.test/a \t", "HtTp://example.test/a"},
		{"HTTPS://example.test", "HTTPS://example.test"},
		{"mAiLtO:person@example.test", "mAiLtO:person@example.test"},
		{"https://example.test/javascript:literal", "https://example.test/javascript:literal"},
	} {
		if got, ok := SafeURL(c.raw); !ok || got != c.want {
			t.Errorf("SafeURL(%q) = %q, %v; want %q, true", c.raw, got, ok, c.want)
		}
	}
	for _, raw := range []string{
		"", "example.test", "/relative", "//example.test",
		"javascript:alert(1)", "data:text/plain,hello",
		"javascript:https://example.test", "httpsx://example.test",
		"https ://example.test", "ht\ttps://example.test", ":https://example.test",
		"\u00a0https://example.test", "\u2003https://example.test", "ＨＴＴＰＳ://example.test",
	} {
		if got, ok := SafeURL(raw); ok {
			t.Errorf("SafeURL(%q) = %q, true; want rejected", raw, got)
		}
	}
	if got, ok := SafeURL("https://example.test/\u00a0"); !ok || got != "https://example.test/\u00a0" {
		t.Errorf("non-ASCII trailing whitespace must not be trimmed: %q, %v", got, ok)
	}
}
