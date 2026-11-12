package class_test

import (
	"testing"

	parser "github.com/gosuda/elegant-mermaid/internal/syntax/class"
)

func TestUnicodeNames(t *testing.T) {
	for _, name := range []string{"Café", "动物", "\u9fcc"} {
		_, ds := parser.Parse([]byte("classDiagram\nclass "+name+"\n"), nil)
		if len(ds) > 0 {
			t.Fatal(name, ds)
		}
	}
	for _, name := range []string{"😀", "\u9fcd", "\u1c90"} {
		_, ds := parser.Parse([]byte("classDiagram\nclass "+name+"\n"), nil)
		if len(ds) == 0 {
			t.Fatal("accepted non-authority letter", name)
		}
	}
}

func TestTokenSourceBorrowing(t *testing.T) {
	src := []byte("classDiagram\nclass `A B`~T~\n")
	tokens := parser.Lex(src, nil)
	for _, token := range tokens {
		if len(token.Raw) == 0 {
			continue
		}
		if &token.Raw[0] != &src[token.Span.Start] {
			t.Fatal(token)
		}
	}
	if tokens[2].Text != "class" || tokens[3].Text != "A B" || tokens[4].Text != "T" {
		t.Fatal(tokens)
	}
}
