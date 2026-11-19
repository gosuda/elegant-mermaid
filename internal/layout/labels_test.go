package layout

import "testing"

func TestBoxLabelDefaults(t *testing.T) {
	cases := []struct {
		source string
		count  int
		text   string
	}{
		{"flowchart\nA --> B\n", 0, ""},
		{"flowchart\nA[\"\"]\n", 1, ""},
		{"flowchart\nA[A]\n", 0, ""},
		{"flowchart\nA@{label: \"\"}\n", 1, ""},
	}
	for _, c := range cases {
		in, ok := inputSource(t, []byte(c.source))
		if !ok {
			t.Fatalf("rejected %s", c.source)
		}
		if len(in.Labels) != c.count {
			t.Fatalf("%s: labels %#v", c.source, in.Labels)
		}
		if c.count > 0 && in.Labels[0].Text != c.text {
			t.Fatal(in.Labels)
		}
	}
}
