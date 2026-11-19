package journey

import (
	"slices"
	"strconv"
	"strings"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/journey"
)

const (
	codeUnexpected = "journey/unexpected-token"
	codeOutOfRange = "journey/score-out-of-range"
	scoreMinName   = "vector.journey.score_min"
	scoreMaxName   = "vector.journey.score_max"
	maxExactDigits = 18
)

type resolver struct {
	model   *Model
	current Section
	lo, hi  int64
	diags   []diag.Diagnostic
}

func Resolve(src []byte, document *syn.Start) (*Model, []diag.Diagnostic) {
	r := &resolver{model: &Model{HeaderSpan: document.Header.Span, Config: readConfig(src)}}
	r.lo, r.hi = scoreRange()
	for _, line := range document.Document.Lines {
		if line.Statement != nil {
			r.statement(line.Statement)
		}
	}
	r.model.Actors = actors(r.model.Tasks)
	return r.model, r.diags
}

func scoreRange() (int64, int64) {
	var lo, hi int64
	for i := range gen.LayoutConst {
		switch gen.LayoutConst[i].Name {
		case scoreMinName:
			lo = int64(gen.LayoutConst[i].Value)
		case scoreMaxName:
			hi = int64(gen.LayoutConst[i].Value)
		}
	}
	return lo, hi
}

func (r *resolver) statement(s *syn.Statement) {
	m := r.model
	switch node := s.Kind.(type) {
	case *syn.Title:
		m.Title, m.TitleLabel, m.TitleSpan = node.Text.Text, label(node.Text.Text), node.Text.Span
	case *syn.AccTitle:
		m.AccTitle = syn.Trim(node.Value.Text)
	case *syn.AccDescr:
		m.AccDescr = description(node.Value.Text)
	case *syn.AccDescrMultiline:
		m.AccDescr = description(node.Value.Text)
	case *syn.Section:
		r.current = Section{Name: node.Text.Text, Label: label(node.Text.Text), Span: node.Text.Span}
		m.Sections = append(m.Sections, r.current)
	case *syn.Task:
		r.task(s.Span, node)
	}
}

func (r *resolver) task(span source.Span, node *syn.Task) {
	score, scoreField := r.score(node.Fields[0])
	t := Task{
		Section:      r.current.Name,
		SectionLabel: r.current.Label,
		SectionSpan:  r.current.Span,
		Name:         node.Name.Text,
		Label:        label(node.Name.Text),
		Score:        score,
		Span:         span,
		NameSpan:     node.Name.Span,
		ScoreSpan:    scoreField,
		WithoutActor: len(node.Fields) < 2 || strings.Trim(node.Fields[1].Raw.Text, " ,\t\r\n") == "",
	}
	if len(node.Fields) > 1 {
		t.ActorSpan = node.Fields[1].Raw.Span
		for name := range strings.SplitSeq(node.Fields[1].Raw.Text, ",") {
			t.People = append(t.People, syn.Trim(name))
		}
	}
	r.model.Tasks = append(r.model.Tasks, t)
}

func (r *resolver) score(field syn.Field) (int, source.Span) {
	text, span := field.Trimmed.Text, field.Trimmed.Span
	digits := strings.TrimLeft(text, "+-")
	if len(text)-len(digits) > 1 || digits == "" || strings.Trim(digits, "0123456789") != "" {
		r.diags = append(r.diags, syn.Diagnostic(codeUnexpected, "unexpected "+text+", expected one of: integer", span))
		return 0, span
	}
	value, ok := integerValue(text[:len(text)-len(digits)], digits)
	if !ok || value < r.lo || value > r.hi {
		message := "score " + text + " is outside the range " + strconv.FormatInt(r.lo, 10) + " to " + strconv.FormatInt(r.hi, 10)
		r.diags = append(r.diags, syn.Diagnostic(codeOutOfRange, message, span))
		return 0, span
	}
	return int(value), span
}

func integerValue(sign, digits string) (int64, bool) {
	digits = strings.TrimLeft(digits, "0")
	if len(digits) > maxExactDigits {
		return 0, false
	}
	if digits == "" {
		return 0, true
	}
	value, err := strconv.ParseInt(digits, 10, 64)
	if sign == "-" {
		value = -value
	}
	return value, err == nil
}

func actors(tasks []Task) []string {
	var names []string
	for _, t := range tasks {
		for _, name := range t.People {
			if !slices.Contains(names, name) {
				names = append(names, name)
			}
		}
	}
	slices.SortFunc(names, compareUTF16)
	return names
}

func compareUTF16(a, b string) int {
	return slices.Compare(utf16.Encode([]rune(a)), utf16.Encode([]rune(b)))
}

func readConfig(src []byte) Config {
	pre := syntax.Preprocess(src)
	var config Config
	for _, block := range []syntax.ConfigValue{pre.Config, pre.Init} {
		readBlock(&config, block)
	}
	return config
}

func readBlock(config *Config, block syntax.ConfigValue) {
	if block.Kind != syntax.ValueMapping {
		return
	}
	i := slices.IndexFunc(block.Entries, func(e syntax.ConfigEntry) bool { return e.Key == "journey" })
	if i < 0 || block.Entries[i].Value.Kind != syntax.ValueMapping {
		return
	}
	for _, field := range block.Entries[i].Value.Entries {
		readField(config, field)
	}
}

func readField(config *Config, field syntax.ConfigEntry) {
	value, err := strconv.ParseInt(field.Value.Text, 10, 64)
	if field.Value.Kind != syntax.ValueInteger || err != nil || value < 0 {
		return
	}
	switch field.Key {
	case "width":
		config.Width, config.WidthSet = value, true
	case "height":
		config.Height, config.HeightSet = value, true
	case "diagramMarginX":
		config.MarginX, config.MarginXSet = value, true
	}
}

func description(text string) string {
	text = syn.Trim(text)
	var out strings.Builder
	for i := 0; i < len(text); {
		c := text[i]
		out.WriteByte(c)
		i++
		if c != '\n' {
			continue
		}
		for i < len(text) {
			r, n := utf8.DecodeRuneInString(text[i:])
			if !syn.IsSpace(r) {
				break
			}
			i += n
		}
	}
	return out.String()
}

func label(text string) string { return syntax.DecodeEntities(syn.Trim(text)) }
