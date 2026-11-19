package class

import (
	"strings"

	syn "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func (r *resolver) style(kind string, statement *syn.StyleStatement) {
	if kind == "classDef" {
		for _, name := range statement.Targets {
			r.definition(name, statement.Text)
		}
		return
	}
	for _, id := range statement.Targets {
		i := r.index(strings.TrimSpace(id))
		if i < 0 {
			continue
		}
		if kind == "cssClass" {
			r.model.Classes[i].CSS += " " + statement.Text
		} else {
			r.model.Classes[i].Styles = append(r.model.Classes[i].Styles, statement.Text)
		}
	}
}

func (r *resolver) definition(name, style string) {
	i := r.definitionIndex(name)
	r.model.Definitions[i].Styles = append(r.model.Definitions[i].Styles, style)
	var textStyle string
	if strings.Contains(style, "color") {
		textStyle = strings.ReplaceAll(style, "fill", "bgFill")
		r.model.Definitions[i].TextStyles = append(r.model.Definitions[i].TextStyles, textStyle)
	}
	for j := range r.model.Classes {
		c := &r.model.Classes[j]
		if !strings.Contains(c.CSS, name) {
			continue
		}
		c.Styles = append(c.Styles, style)
		if textStyle != "" {
			c.TextStyles = append(c.TextStyles, textStyle)
		}
	}
}

func (r *resolver) definitionIndex(name string) int {
	for i, definition := range r.model.Definitions {
		if definition.Name == name {
			return i
		}
	}
	r.model.Definitions = append(r.model.Definitions, StyleDefinition{Name: name})
	return len(r.model.Definitions) - 1
}

func (r *resolver) click(c *syn.ClickStatement) {
	if r.index(c.Name.Value) < 0 {
		return
	}
	args := callbackArguments(c.Arguments)
	if len(args) == 0 {
		args = []string{c.Name.Value}
	}
	click := Click{Target: c.Name.Value, Action: c.Action, Value: c.Value, Arguments: c.Arguments, Tooltip: c.Tooltip, LinkTarget: c.Target, Args: args}
	for i := range r.model.Clicks {
		if r.model.Clicks[i].Target == c.Name.Value {
			r.model.Clicks[i] = click
			return
		}
	}
	r.model.Clicks = append(r.model.Clicks, click)
}

func callbackArguments(text string) []string {
	var out []string
	start := 0
	quoted := false
	for i, ch := range text {
		if ch == '"' {
			quoted = !quoted
		}
		if ch == ',' && !quoted {
			out = append(out, callbackArgument(text[start:i]))
			start = i + 1
		}
	}
	if rest := strings.TrimSpace(text[start:]); rest != "" {
		out = append(out, callbackArgument(rest))
	}
	return out
}

func callbackArgument(text string) string {
	text = strings.TrimSpace(text)
	if value, found := strings.CutPrefix(text, "\""); found {
		if value, found = strings.CutSuffix(value, "\""); found {
			return value
		}
	}
	return text
}
