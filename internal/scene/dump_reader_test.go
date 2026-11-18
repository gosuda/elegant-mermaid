package scene

import (
	"errors"
	"strings"
	"testing"
)

const readerDump = `{"version":1,"stage":"layout","kind":"flowchart","profile":"vector","options":{"direction":"LR"},"canvas":{"w":100,"h":50},"boxes":[{"id":"A","role":"node","x":10,"y":10,"w":20,"h":10,"parent":"","exclusive":true},{"id":"B","role":"node","x":60,"y":10,"w":20,"h":10,"parent":"","exclusive":true}],"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[[30,15],[60,15]]}],"labels":[{"id":"e0.label","owner":"e0","text":"yes","x":35,"y":5,"w":10,"h":5,"lines":["yes"]}]}`

type dumpEdit struct{ old, new string }

func editedDump(t *testing.T, edits []dumpEdit) string {
	t.Helper()
	text := readerDump
	for _, e := range edits {
		if !strings.Contains(text, e.old) {
			t.Fatalf("the base dump has no %q", e.old)
		}
		text = strings.Replace(text, e.old, e.new, 1)
	}
	return text
}

func TestReadMetricDumpReasons(t *testing.T) {
	for _, c := range []struct {
		name   string
		edits  []dumpEdit
		reason string
	}{
		{"missing version", []dumpEdit{{`"version":1,`, ``}}, "missing version"},
		{"other version", []dumpEdit{{`"version":1`, `"version":2`}}, "expected version 1 layout dump"},
		{"version text", []dumpEdit{{`"version":1`, `"version":"1"`}}, "expected integer"},
		{"version past int32", []dumpEdit{{`"version":1`, `"version":99999999999`}}, "invalid integer"},
		{"model stage", []dumpEdit{{`"stage":"layout"`, `"stage":"model"`}}, "expected version 1 layout dump"},
		{"cell profile", []dumpEdit{{`"profile":"vector"`, `"profile":"cell"`}}, "--metrics needs --profile vector"},
		{"TD direction", []dumpEdit{{`"direction":"LR"`, `"direction":"TD"`}}, "invalid direction"},
		{"missing direction", []dumpEdit{{`"direction":"LR"`, `"x":0`}}, "missing direction"},
		{"options array", []dumpEdit{{`"options":{"direction":"LR"}`, `"options":[]`}}, "expected object"},
		{"negative canvas", []dumpEdit{{`"w":100`, `"w":-1`}}, "canvas has an invalid rectangle"},
		{"huge canvas", []dumpEdit{{`"w":100`, `"w":600000000`}}, "canvas has a coordinate beyond the limit"},
		{"canvas text", []dumpEdit{{`"h":50`, `"h":"3"`}}, "expected integer"},
		{"box role", []dumpEdit{{`"role":"node"`, `"role":"frame"`}}, "invalid box role"},
		{"box id number", []dumpEdit{{`"id":"A"`, `"id":5`}}, "expected string"},
		{"fractional x", []dumpEdit{{`"x":10`, `"x":10.0`}}, "expected integer"},
		{"x past int32", []dumpEdit{{`"x":10`, `"x":3000000000`}}, "invalid integer"},
		{"negative box width", []dumpEdit{{`"w":20,"h":10,"parent":""`, `"w":-5,"h":10,"parent":""`}}, "box A has an invalid rectangle"},
		{"box edge past int32", []dumpEdit{{`"x":10,"y":10,"w":20`, `"x":2147483647,"y":10,"w":20`}}, "box A has an invalid rectangle"},
		{"box past the limit", []dumpEdit{{`"x":10,"y":10,"w":20`, `"x":600000000,"y":10,"w":20`}}, "box A has a coordinate beyond the limit"},
		{"exclusive number", []dumpEdit{{`"exclusive":true`, `"exclusive":1`}}, "expected boolean"},
		{"duplicate box", []dumpEdit{{`"id":"B"`, `"id":"A"`}}, "box id A appears twice"},
		{"unknown parent", []dumpEdit{{`"parent":""`, `"parent":"zzz"`}}, "box A has unknown parent zzz"},
		{"own parent", []dumpEdit{{`"parent":""`, `"parent":"A"`}}, "box A is its own ancestor"},
		{"parent cycle", []dumpEdit{{`"parent":""`, `"parent":"B"`}, {`"parent":""`, `"parent":"A"`}}, "box A is its own ancestor"},
		{"unknown route end", []dumpEdit{{`"to":"B"`, `"to":"zzz"`}}, "route e0 names unknown box zzz"},
		{"duplicate route", []dumpEdit{{`"routes":[`, `"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[]},`}}, "route id e0 appears twice"},
		{"three coordinates", []dumpEdit{{`[60,15]`, `[60,15,1]`}}, "expected point"},
		{"point text", []dumpEdit{{`[60,15]`, `[60,"15"]`}}, "expected integer"},
		{"point not an array", []dumpEdit{{`[60,15]`, `{}`}}, "expected array"},
		{"point past the limit", []dumpEdit{{`[60,15]`, `[600000000,15]`}}, "route e0 has a coordinate beyond the limit"},
		{"unknown label owner", []dumpEdit{{`"owner":"e0"`, `"owner":"zzz"`}}, "label e0.label has unknown owner zzz"},
		{"negative label height", []dumpEdit{{`"h":5,"lines"`, `"h":-5,"lines"`}}, "label e0.label has an invalid rectangle"},
		{"line number", []dumpEdit{{`"lines":["yes"]`, `"lines":[1]`}}, "expected string"},
		{"missing lines", []dumpEdit{{`,"lines":["yes"]`, ``}}, "missing lines"},
		{"first fault wins", []dumpEdit{{`"w":100`, `"w":-1`}, {`"parent":""`, `"parent":"zzz"`}}, "canvas has an invalid rectangle"},
		{"duplicates before relations", []dumpEdit{{`"id":"B"`, `"id":"A"`}, {`"to":"B"`, `"to":"zzz"`}}, "box id A appears twice"},
		{"trailing text", []dumpEdit{{`}]}`, `}]} x`}}, "invalid JSON"},
		{"single quote outside strings", []dumpEdit{{`"version"`, `'version'`}}, "invalid JSON"},
	} {
		t.Run(c.name, func(t *testing.T) {
			_, err := ReadMetricDump([]byte(editedDump(t, c.edits)))
			malformed, ok := errors.AsType[*MalformedError](err)
			if !ok || malformed.Reason != c.reason || !errors.Is(err, ErrMalformed) {
				t.Fatalf("err = %v; want reason %q", err, c.reason)
			}
		})
	}
}

func TestReadMetricDumpRejectsInput(t *testing.T) {
	for name, c := range map[string]struct{ data, reason string }{
		"empty":         {"", "invalid JSON"},
		"array":         {"[]", "invalid JSON"},
		"empty object":  {"{}", "missing version"},
		"invalid UTF-8": {"{\"version\":1,\"x\":\"\xff\"}", "invalid UTF-8"},
		"byte order":    {"\xef\xbb\xbf" + readerDump, "invalid JSON"},
		"capitalised":   {strings.Replace(readerDump, `"version"`, `"Version"`, 1), "missing version"},
	} {
		t.Run(name, func(t *testing.T) {
			_, err := ReadMetricDump([]byte(c.data))
			malformed, ok := errors.AsType[*MalformedError](err)
			if !ok || malformed.Reason != c.reason {
				t.Fatalf("err = %v; want reason %q", err, c.reason)
			}
		})
	}
}

func TestReadMetricDumpAccepts(t *testing.T) {
	for name, edits := range map[string][]dumpEdit{
		"base":              nil,
		"apostrophe":        {{`"text":"yes"`, `"text":"it's"`}},
		"unicode escape":    {{`"text":"yes"`, `"text":"\u00e9"`}},
		"label owner a box": {{`"owner":"e0"`, `"owner":"A"`}},
		"unknown member":    {{`"kind":"flowchart"`, `"kind":5,"extra":[1,{"a":null}]`}},
		"no kind":           {{`"kind":"flowchart",`, ``}},
	} {
		t.Run(name, func(t *testing.T) {
			if _, err := ReadMetricDump([]byte(editedDump(t, edits))); err != nil {
				t.Fatal(err)
			}
		})
	}
}
