package class

import (
	"regexp"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

var methodPattern = regexp.MustCompile(`^([#+~-])?(.+)\((.*)\)([\s$*])?(.*)([$*])?$`)

func ParseMember(text string, span source.Span) Member {
	text = strings.TrimSpace(text)
	m := Member{Text: text, Name: text, Span: span}
	if strings.ContainsAny(text[:min(1, len(text))], "#+~-") {
		m.Visibility, m.Name = text[:1], text[1:]
	}
	m.Static, m.Abstract = strings.HasSuffix(text, "$"), strings.HasSuffix(text, "*")
	parts := methodPattern.FindStringSubmatch(text)
	if len(parts) > 0 {
		parseMethod(&m, parts)
	} else {
		m.Name = memberName(strings.TrimRight(m.Name, "$*"))
		m.Text = m.Visibility + genericText(m.Name)
	}
	m.Text = decodeEntities(m.Text)
	return m
}

func parseMethod(m *Member, parts []string) {
	m.Method, m.Visibility = true, parts[1]
	m.Name, m.Parameters = memberName(parts[2]), strings.TrimSpace(parts[3])
	m.ReturnType = strings.TrimSpace(strings.TrimRight(parts[5], "$*"))
	m.Text = m.Visibility + genericText(m.Name) + "(" + genericText(m.Parameters) + ")"
	if m.ReturnType != "" {
		m.Text += " : " + genericText(m.ReturnType)
	}
	classifier := parts[4] + parts[6]
	m.Static = m.Static || strings.Contains(classifier, "$")
	m.Abstract = m.Abstract || strings.Contains(classifier, "*")
}

func memberName(name string) string {
	trimmed := strings.TrimLeft(name, " ")
	if len(trimmed) != len(name) {
		return " " + trimmed
	}
	return name
}

func genericText(text string) string {
	var out strings.Builder
	for {
		before, rest, found := strings.Cut(text, "~")
		out.WriteString(before)
		if !found {
			break
		}
		generic, after, paired := strings.Cut(rest, "~")
		if !paired {
			out.WriteByte('~')
			out.WriteString(rest)
			break
		}
		out.WriteByte('<')
		out.WriteString(generic)
		out.WriteByte('>')
		text = after
	}
	return out.String()
}
