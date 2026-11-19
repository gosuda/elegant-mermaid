package theme

import (
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

type Token uint8

const (
	Background Token = iota
	Foreground
	Line
	Accent
	Muted
	Surface
	Border
	Series0
	Series1
	Series2
	Series3
	Series4
	Series5
	Series6
	Series7
	Series8
	Series9
	Series10
	Series11
	Error
	Warning
	Success
	tokenCount
)

func (t Token) String() string {
	names := [...]string{"bg", "fg", "line", "accent", "muted", "surface", "border", "series0", "series1", "series2", "series3", "series4", "series5", "series6", "series7", "series8", "series9", "series10", "series11", "error", "warning", "success"}
	if t >= tokenCount {
		return ""
	}
	return names[t]
}

type UnknownThemeError struct{ Name string }

func (e *UnknownThemeError) Error() string { return fmt.Sprintf("unknown theme: %s", e.Name) }

type TextChoice uint8

const (
	TextForeground TextChoice = iota
	TextBackground
	TextPlate
)

type Theme struct {
	name    string
	colours [tokenCount]Colour
	strokes [tokenCount]Token
	text    [12]TextChoice
}

func Resolve(name string) (Theme, error) {
	if name == "" {
		name = "elegant-light"
	}
	for _, row := range gen.Themes {
		if row.Name == name {
			return resolveRow(row)
		}
	}
	return Theme{}, &UnknownThemeError{Name: name}
}

func Names() []string {
	names := make([]string, len(gen.Themes))
	for i, row := range gen.Themes {
		names[i] = row.Name
	}
	return names
}

func resolveRow(row gen.Theme) (Theme, error) {
	t := Theme{name: row.Name}
	for token := range tokenCount {
		t.strokes[token] = token
		for _, value := range row.Tokens {
			if value.Token != token.String() {
				continue
			}
			c, err := ParseHex(value.Value)
			if err != nil {
				return Theme{}, err
			}
			t.colours[token] = c
		}
	}
	t.loadChoices()
	return t, nil
}

func (t *Theme) loadChoices() {
	for _, row := range gen.StrokeOk {
		if row.Theme != t.name || row.OK != 0 {
			continue
		}
		for token := range tokenCount {
			if token.String() == row.Token {
				t.strokes[token] = Line
			}
		}
	}
	for _, row := range gen.SeriesText {
		if row.Theme == t.name {
			t.text[row.Series] = TextChoice(row.Choice)
		}
	}
}

func (t Theme) Name() string { return t.name }
func (t Theme) Colour(token Token) Colour {
	if token >= tokenCount {
		return Colour{}
	}
	return t.colours[token]
}

func (t Theme) Stroke(token Token) Token {
	if token >= tokenCount {
		return Line
	}
	return t.strokes[token]
}
func (t Theme) SeriesText(index uint8) TextChoice { return t.text[index%12] }
