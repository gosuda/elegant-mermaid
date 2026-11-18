package theme_test

import (
	"encoding/json"
	"os"
	"slices"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/theme"
)

type specTheme struct {
	Name   string            `json:"name"`
	Tokens map[string]string `json:"tokens"`
}

func loadSpecThemes(t *testing.T) []specTheme {
	t.Helper()
	data, err := os.ReadFile("../../spec/data/themes.json")
	if err != nil {
		t.Fatal(err)
	}
	var rows []specTheme
	if err := json.Unmarshal(data, &rows); err != nil {
		t.Fatal(err)
	}
	return rows
}

func TestNamesAreSpecThemes(t *testing.T) {
	rows := loadSpecThemes(t)
	want := make([]string, len(rows))
	for i, row := range rows {
		want[i] = row.Name
	}
	slices.Sort(want)
	got := theme.Names()
	if len(want) != 20 || !slices.Equal(got, want) {
		t.Fatalf("theme names %q, want the %d sorted names of spec/data/themes.json %q", got, len(want), want)
	}
}

func TestEverySpecThemeTokenResolves(t *testing.T) {
	for _, row := range loadSpecThemes(t) {
		th, err := theme.Resolve(row.Name)
		if err != nil {
			t.Fatalf("%s: %v", row.Name, err)
		}
		if th.Name() != row.Name {
			t.Fatalf("resolved %q as %q", row.Name, th.Name())
		}
		for token := theme.Background; token.String() != ""; token++ {
			want, ok := row.Tokens[token.String()]
			if !ok {
				t.Fatalf("%s: spec lacks token %s", row.Name, token)
			}
			if got := th.Colour(token).Hex(); got != want {
				t.Fatalf("%s %s: %s, want %s", row.Name, token, got, want)
			}
		}
	}
}
