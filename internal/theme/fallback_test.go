package theme_test

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/theme"
)

func TestSpecifiedFallbacks(t *testing.T) {
	cases := []struct {
		name   string
		tokens []theme.Token
	}{
		{"catppuccin-latte", []theme.Token{theme.Warning, theme.Success, theme.Series0, theme.Series2, theme.Series3, theme.Series4, theme.Series6, theme.Series7, theme.Series8, theme.Series10}},
		{"nord", []theme.Token{theme.Error, theme.Series1, theme.Series3, theme.Series5, theme.Series9, theme.Series11}},
		{"solarized-light", []theme.Token{theme.Success, theme.Series0, theme.Series2, theme.Series4, theme.Series6, theme.Series7, theme.Series8, theme.Series10}},
		{"solarized-dark", []theme.Token{theme.Error, theme.Warning, theme.Series1, theme.Series5, theme.Series9, theme.Series11}},
		{"elegant-light", []theme.Token{theme.Series0, theme.Series2, theme.Series4, theme.Series6, theme.Series7, theme.Series8, theme.Series10}},
		{"github-light", []theme.Token{theme.Series0, theme.Series2, theme.Series4, theme.Series6, theme.Series7, theme.Series8, theme.Series10}},
		{"elegant-dark", []theme.Token{theme.Series9}},
		{"github-dark", []theme.Token{theme.Series9}},
		{"catppuccin-mocha", []theme.Token{theme.Series9}},
	}
	for _, tc := range cases {
		th, err := theme.Resolve(tc.name)
		if err != nil {
			t.Fatal(err)
		}
		for _, token := range tc.tokens {
			if th.Stroke(token) != theme.Line {
				t.Errorf("%s %s must fall back", tc.name, token)
			}
		}
	}
}
