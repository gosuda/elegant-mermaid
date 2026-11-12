package markdown

import (
	"bytes"
	"reflect"
	"testing"
)

func TestBlocks(t *testing.T) {
	cases := []struct{ name, host, want string }{
		{"backtick", "```mermaid\nflowchart LR\n```\n", "flowchart LR\n"},
		{"tilde", "~~~mmd\nx\n~~~~\n", "x\n"},
		{"unclosed", "```Mermaid\nx", "x"},
		{"quote", "> ```MMD\n> x\n> ```\ny\n", "x\n"},
		{"list", "- x\n  ```mermaid\n  x\n  ```\n", "x\n"},
		{"nested", "> - x\n>   ```mermaid\n>   flowchart LR\n>     A --> B\n>   ```\n", "flowchart LR\n  A --> B\n"},
		{"quoteInList", "- x\n  > ```mermaid\n  > x\n  > ```\n", "x\n"},
		{"tab", "-\tx\n\t```mermaid\n\tx\n\t```\n", "x\n"},
		{"colon", ":::mermaid\nx\n:::\n", "x\n"},
		{"crlf", "```{mermaid}\r\nx\r\n```\r\n", "x\r\n"},
		{"containerEnd", "> ```mermaid\n> x\ny\n", "x\n"},
		{"empty", "```mermaid\n```\n", ""},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			host := []byte(c.host)
			blocks := Blocks(host)
			if len(blocks) != 1 {
				t.Fatalf("blocks=%v", blocks)
			}
			b := blocks[0]
			if string(b.Source) != c.want {
				t.Fatalf("source=%q want=%q", b.Source, c.want)
			}
			checkMapping(t, host, b)
		})
	}
}

func checkMapping(t testing.TB, host []byte, b Block) {
	t.Helper()
	for _, l := range b.Lines {
		checkLineMapping(t, host, b, l)
	}
	if b.Span.Start < 0 || b.Span.End < b.Span.Start || b.Span.End > len(host) {
		t.Fatalf("span=%+v", b.Span)
	}
}

func checkLineMapping(t testing.TB, host []byte, b Block, l BlockLine) {
	t.Helper()
	if l.HostOffset < 0 || l.Len < 0 || l.HostOffset+l.Len > len(host) || l.BlockOffset < 0 || l.BlockOffset+l.Len > len(b.Source) {
		t.Fatalf("invalid line: %+v", l)
	}
	for d := range l.Len {
		if host[l.HostOffset+d] != b.Source[l.BlockOffset+d] || b.HostOffset(l.BlockOffset+d) != l.HostOffset+d {
			t.Fatal("mapping differs")
		}
	}
	if b.HostOffset(l.BlockOffset+l.Len) != l.HostOffset+l.Len {
		t.Fatal("line end differs")
	}
}

func TestNestedRecord(t *testing.T) {
	host := []byte("> - x\n>   ```mermaid\n>   flowchart LR\n>     A --> B\n>   ```\n")
	b := Blocks(host)[0]
	want := []BlockLine{{25, 0, 12}, {42, 13, 9}}
	if b.Span.Start != 6 || b.Span.End != 59 || !reflect.DeepEqual(b.Lines, want) {
		t.Fatalf("span=%+v lines=%+v", b.Span, b.Lines)
	}
}

func TestFenceIsolation(t *testing.T) {
	host := []byte("```text\n```mermaid\nx\n```\n~~~mermaid\ny\n~~~\n")
	b := Blocks(host)
	if len(b) != 1 || string(b[0].Source) != "y\n" {
		t.Fatalf("blocks=%+v", b)
	}
}

func TestSourceOwnership(t *testing.T) {
	host := []byte("```mermaid\nx\n```\n")
	b := Blocks(host)[0]
	host[11] = 'z'
	if !bytes.Equal(b.Source, []byte("z\n")) {
		t.Fatal("top-level source must alias")
	}
	host = []byte("> ```mermaid\n> x\n> ```\n")
	b = Blocks(host)[0]
	host[15] = 'z'
	if string(b.Source) != "x\n" {
		t.Fatal("container source must own bytes")
	}
}
