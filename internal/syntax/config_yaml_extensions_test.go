package syntax

import (
	"strings"
	"testing"
)

func TestYAMLBlockSequenceNodes(t *testing.T) {
	src := []byte("items:\n  - key: first\n    other: [true, 2]\n  - - nested\n    - {x: y}\n  -\n  -\n    child:\n      - last\nafter: done\n")
	v, ds := ParseConfigYAML(src, 0, len(src))
	if len(ds) != 0 {
		t.Fatalf("diagnostics: %+v", ds)
	}
	items := v.Entries[0].Value.Items
	if len(items) != 4 || items[0].Kind != ValueMapping || items[1].Kind != ValueSequence || items[2].Kind != ValueNull || items[3].Entries[0].Value.Items[0].Text != "last" {
		t.Fatalf("nodes: %+v", items)
	}
	if v.Entries[1].Value.Text != "done" {
		t.Fatalf("parent consumed: %+v", v)
	}
}

func TestYAMLMultilineValueFolding(t *testing.T) {
	for _, eol := range []string{"\n", "\r\n", "\r"} {
		for _, tc := range []struct{ source, want string }{
			{"value: first  \n  second\n\n  third\nafter: kept\n", "first second\nthird"},
			{"value:\n  first\n  second\nafter: kept\n", "first second"},
			{"value: 'it''s first \n  second\n\n  third'\nafter: kept\n", "it's first second\nthird"},
			{"value: \"first\\\n  second\n\n  third\"\nafter: kept\n", "firstsecond\nthird"},
			{"value: 12\n  34\nafter: kept\n", "12 34"},
			{"value: first line\n  `subroutine` remains plain\nafter: kept\n", "first line `subroutine` remains plain"},
			{"value: first line\n  'neo' remains plain\nafter: kept\n", "first line 'neo' remains plain"},
			{"value: first line\n  \"default\" remains plain # comment\nafter: kept\n", "first line \"default\" remains plain"},
		} {
			src := []byte(strings.ReplaceAll(tc.source, "\n", eol))
			v, ds := ParseConfigYAML(src, 0, len(src))
			if len(ds) != 0 {
				t.Fatalf("%q: %+v", src, ds)
			}
			if v.Entries[0].Value.Text != tc.want || v.Entries[0].Value.Kind != ValueString || v.Entries[1].Value.Text != "kept" {
				t.Fatalf("%q: %+v", src, v)
			}
			span := v.Entries[0].Value.Span
			if span.Start < 0 || span.End > strings.Index(string(src), "after:") || span.End <= span.Start {
				t.Fatalf("span: %+v", span)
			}
		}
	}
}

func TestYAMLSequenceDepthAndProgress(t *testing.T) {
	for _, depth := range []int{64, 65} {
		src := []byte(strings.Repeat("- ", depth) + "leaf\n")
		_, ds := ParseConfigYAML(src, 0, len(src))
		if depth == 64 && len(ds) != 0 {
			t.Fatalf("depth64: %+v", ds)
		}
		if depth == 65 && (len(ds) != 1 || ds[0].Code != "limit/nesting-depth" || ds[0].Span.Start != 128) {
			t.Fatalf("depth65: %+v", ds)
		}
	}
	for _, text := range []string{"- -\n x\n", "a:\n  - &anchor\n  - next\n", "a: 'open\nnext: value\n", "a: one\n\tbad\n"} {
		_, ds := ParseConfigYAML([]byte(text), 0, len(text))
		if len(ds) != 1 {
			t.Fatalf("%q: %+v", text, ds)
		}
	}
}

func TestYAMLExtensionsKeepJSONAndKeysStrict(t *testing.T) {
	for _, text := range []string{"{\"a\":\"first\n second\"}", "{\"a\":\"first\\\n second\"}", "{\"a\": - item}"} {
		_, ds := ParseConfigJSON([]byte(text), 0, len(text))
		if len(ds) == 0 {
			t.Fatalf("JSON accepted %q", text)
		}
	}
	for _, text := range []string{"'first\n  second': value\n", "{ 'first\n  second': value }\n"} {
		_, ds := ParseConfigYAML([]byte(text), 0, len(text))
		if len(ds) == 0 {
			t.Fatalf("key accepted %q", text)
		}
	}
}

func TestYAMLRepresentativeMetadataAndDuplicateSpans(t *testing.T) {
	text := "description:\n  All fork and join aliases\n  should render the same shape.\ncoveredShapes:\n  - fork\n  - join\nconfig:\n  theme: light\n  theme: dark\n"
	v, ds := ParseConfigYAML([]byte(text), 0, len(text))
	if len(ds) != 1 || ds[0].Span.Start != strings.LastIndex(text, "theme:") {
		t.Fatalf("duplicate: %+v", ds)
	}
	if v.Entries[0].Value.Text != "All fork and join aliases should render the same shape." || len(v.Entries[1].Value.Items) != 2 || v.Entries[2].Value.Entries[0].Value.Text != "dark" {
		t.Fatalf("metadata: %+v", v)
	}
}

func TestYAMLMultilineOriginalByteSpans(t *testing.T) {
	text := "prefix\r\nvalue: 'α\r\n  β'\r\nafter: yes\r\nsuffix"
	start := strings.Index(text, "value:")
	end := strings.Index(text, "suffix")
	v, ds := ParseConfigYAML([]byte(text), start, end)
	if len(ds) != 0 {
		t.Fatalf("diagnostics: %+v", ds)
	}
	value := v.Entries[0].Value
	if value.Text != "α β" || value.Span.Start != strings.Index(text, "'α") || value.Span.End != strings.Index(text, "β'")+len("β'") {
		t.Fatalf("value: %+v", value)
	}
}

func TestYAMLFlowMultilineAndBlockChomping(t *testing.T) {
	text := "flow: [first\n  second, 'third\n  fourth']\nliteral: |-\n  one\n  two\nfolded: >-\n  one\n  two\n"
	v, ds := ParseConfigYAML([]byte(text), 0, len(text))
	if len(ds) != 0 {
		t.Fatalf("diagnostics: %+v", ds)
	}
	if v.Entries[0].Value.Items[0].Text != "first second" || v.Entries[0].Value.Items[1].Text != "third fourth" || v.Entries[1].Value.Text != "one\ntwo" || v.Entries[2].Value.Text != "one two" {
		t.Fatalf("values: %+v", v)
	}
}

func TestYAMLPlainFoldingKeepsScalarTokensAndSpans(t *testing.T) {
	text := "single: true\nfolded: true\n  false\nflow: [missing , 'quoted', \"double\"]\n"
	value, ds := ParseConfigYAML([]byte(text), 0, len(text))
	if len(ds) != 0 {
		t.Fatalf("diagnostics: %+v", ds)
	}
	if value.Entries[0].Value.Kind != ValueBool || !value.Entries[0].Value.Bool {
		t.Fatalf("single scalar: %+v", value.Entries[0].Value)
	}
	if value.Entries[1].Value.Text != "true false" {
		t.Fatalf("folded scalar: %+v", value.Entries[1].Value)
	}
	items := value.Entries[2].Value.Items
	for i, want := range []string{"missing", "'quoted'", "\"double\""} {
		got := items[i]
		if string([]byte(text)[got.Span.Start:got.Span.End]) != want {
			t.Fatalf("item %d span: %+v", i, got)
		}
	}
}
