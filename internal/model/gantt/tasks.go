package gantt

import (
	"strconv"
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/source"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/gantt"
)

const codeTaskData = "gantt/task-data-invalid"

type field struct {
	text string
	span source.Span
}

var tagTable = [...]struct {
	name string
	set  func(*Task)
}{
	{"active", func(t *Task) { t.Active = true }},
	{"done", func(t *Task) { t.Done = true }},
	{"crit", func(t *Task) { t.Crit = true }},
	{"milestone", func(t *Task) { t.Milestone = true }},
	{"vert", func(t *Task) { t.Vert = true }},
}

func asciiLower(text string) string {
	out := []byte(text)
	for i, c := range out {
		if c >= 'A' && c <= 'Z' {
			out[i] = c + 'a' - 'A'
		}
	}
	return string(out)
}

func splitFields(body string, base int) []field {
	var out []field
	from := 0
	for {
		at := strings.IndexByte(body[from:], ',')
		end := len(body)
		if at >= 0 {
			end = from + at
		}
		out = append(out, field{text: body[from:end], span: source.Span{Start: base + from, End: base + end}})
		if at < 0 {
			return out
		}
		from = end + 1
	}
}

func (f field) trimmed() field {
	lead := len(f.text) - len(strings.TrimLeftFunc(f.text, syn.IsSpace))
	body := strings.TrimFunc(f.text, syn.IsSpace)
	start := f.span.Start + lead
	return field{text: body, span: source.Span{Start: start, End: start + len(body)}}
}

func consumeTags(t *Task, fields []field) []field {
	for matched := true; matched; {
		matched = false
		for _, tag := range tagTable {
			if len(fields) > 0 && trim(fields[0].text) == tag.name {
				tag.set(t)
				fields = fields[1:]
				matched = true
			}
		}
	}
	return fields
}

func (r *resolver) addTask(node *syn.Task, span source.Span) {
	data := node.Data
	body := strings.TrimPrefix(data.Value, ":")
	t := Task{Text: node.Text.Value, Label: label(node.Text.Value), Section: NoSection, Span: span, DataSpan: data.Span, Order: -1}
	if n := len(r.model.Sections); n > 0 {
		t.Section = n - 1
	}
	fields := consumeTags(&t, splitFields(body, data.Span.Start+1))
	if len(fields) < 1 || len(fields) > 3 {
		r.report(codeTaskData, "task requires one, two, or three data fields after tags", data.Span)
		return
	}
	for i := range fields {
		fields[i] = fields[i].trimmed()
	}
	switch len(fields) {
	case 1:
		t.ID, t.Generated = r.generatedID(), true
		t.StartKind, t.PrevID, t.HasPrev = startPrevEnd, r.lastID, r.hasLast
		t.End = Operand{fields[0].text, fields[0].span}
	case 2:
		t.ID, t.Generated = r.generatedID(), true
		t.Start, t.End = Operand{fields[0].text, fields[0].span}, Operand{fields[1].text, fields[1].span}
	default:
		t.ID = fields[0].text
		t.Start, t.End = Operand{fields[1].text, fields[1].span}, Operand{fields[2].text, fields[2].span}
	}
	if !t.Vert {
		t.Order = r.order
		r.order++
	}
	m := r.model
	m.Tasks = append(m.Tasks, t)
	m.Rows = append(m.Rows, Row{Kind: RowTask, Index: len(m.Tasks) - 1})
	r.ids[t.ID] = len(m.Tasks) - 1
	r.lastID, r.hasLast = t.ID, true
}

func (r *resolver) generatedID() string {
	r.counter++
	return "task" + strconv.Itoa(r.counter)
}
