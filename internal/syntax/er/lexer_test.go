package er

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/source"
)

func kinds(tokens []Token, match func(Token) bool) []string {
	var out []string
	for _, t := range tokens {
		if match(t) {
			out = append(out, t.Text)
		}
	}
	return out
}

func TestAttributeGenericsGreedAndMultilineBackticks(t *testing.T) {
	tokens := Lex([]byte("erDiagram\nA { List~T~ value\n`line\r\nname` item }"), nil)
	words := kinds(tokens, func(t Token) bool { return t.Kind == "ATTRIBUTE_WORD" })
	want := []string{"List~T~", "value", "line\r\nname", "item"}
	if len(words) != len(want) {
		t.Fatal(words)
	}
	for i := range want {
		if words[i] != want[i] {
			t.Fatal(i, words)
		}
	}
	for _, tok := range tokens {
		if tok.Text == "line\r\nname" {
			if tok.Span != (source.Span{Start: 28, End: 40}) {
				t.Fatal(tok)
			}
			return
		}
	}
	t.Fatal("backtick token missing")
}

func TestCardinalitySpellingsFollowOrderedRules(t *testing.T) {
	for _, pair := range [][2]string{
		{"one or zero", "ZERO_OR_ONE"},
		{"one or more", "ONE_OR_MORE"},
		{"one or many", "ONE_OR_MORE"},
		{"1+", "ONE_OR_MORE"},
		{"|o", "ZERO_OR_ONE"},
		{"zero or one", "ZERO_OR_ONE"},
		{"zero or more", "ZERO_OR_MORE"},
		{"zero or many", "ZERO_OR_MORE"},
		{"0+", "ZERO_OR_MORE"},
		{"}o", "ZERO_OR_MORE"},
		{"many(0)", "ZERO_OR_MORE"},
		{"many(1)", "ONE_OR_MORE"},
		{"many", "ZERO_OR_MORE"},
		{"}|", "ONE_OR_MORE"},
		{"one", "ONLY_ONE"},
		{"only one", "ONLY_ONE"},
		{"||", "ONLY_ONE"},
		{"o|", "ZERO_OR_ONE"},
		{"o{", "ZERO_OR_MORE"},
		{"|{", "ONE_OR_MORE"},
	} {
		tokens := Lex([]byte(pair[0]), nil)
		if len(tokens) == 0 || tokens[0].Kind != pair[1] || tokens[0].Text != pair[0] || tokens[0].Span != (source.Span{Start: 0, End: len(pair[0])}) {
			t.Fatal(pair, tokens)
		}
	}
}

func TestNumericEntityOneUsesNonConsumingLookahead(t *testing.T) {
	tokens := Lex([]byte("1\n1 A\n1 2\n1--\n1..\n1.-\n1-.\n1.25\n12"), nil)
	var numbers []string
	for _, tok := range tokens {
		switch tok.Kind {
		case "ONLY_ONE", "ENTITY_ONE", "NUM", "DECIMAL_NUM":
			numbers = append(numbers, tok.Kind+" "+tok.Text)
		}
	}
	want := []string{
		"ONLY_ONE 1",
		"ONLY_ONE 1",
		"ONLY_ONE 1",
		"NUM 2",
		"ONLY_ONE 1",
		"ONLY_ONE 1",
		"ONLY_ONE 1",
		"ONLY_ONE 1",
		"DECIMAL_NUM 1.25",
		"ENTITY_ONE 1",
		"NUM 2",
	}
	if len(numbers) != len(want) {
		t.Fatal(numbers)
	}
	for i := range want {
		if numbers[i] != want[i] {
			t.Fatal(i, numbers)
		}
	}
	found := false
	for _, tok := range tokens {
		if tok.Kind == "UNICODE_TEXT" && tok.Text == "A" {
			found = true
		}
	}
	if !found {
		t.Fatal("lookahead consumed the entity token")
	}
}

func TestRemovedSpansAreSkippedWithoutRebasing(t *testing.T) {
	text := []byte("ignored\nerDiagram\rA")
	tokens := Lex(text, []source.Span{{Start: 0, End: 8}})
	if len(tokens) == 0 || tokens[0].Kind != "ER_DIAGRAM" || tokens[0].Span != (source.Span{Start: 8, End: 17}) {
		t.Fatal(tokens)
	}
	for _, tok := range tokens {
		if !isBoundary(text, tok.Span.Start) || !isBoundary(text, tok.Span.End) {
			t.Fatal(tok)
		}
	}
}

func isBoundary(src []byte, at int) bool {
	return at == 0 || at >= len(src) || src[at]&0xC0 != 0x80
}

func TestSingleModeKeyAndKeywordPrefixPrecedence(t *testing.T) {
	tokens := Lex([]byte("erDiagram\nA { PKfoo id FK,UK\n}\nstyleNode fill:red\n"), nil)
	wantFields(t, tokens, "ATTRIBUTE_WORD PKfoo", "ATTRIBUTE_WORD id", "ATTRIBUTE_KEY FK", "ATTRIBUTE_KEY UK")
	if !hasToken(tokens, "STYLE", "style") || !hasToken(tokens, "STYLE_TEXT", "Node") {
		t.Fatal("style keyword or suffix missing")
	}
}

func wantFields(t *testing.T, tokens []Token, want ...string) {
	t.Helper()
	var got []string
	for _, tok := range tokens {
		if tok.Kind == "ATTRIBUTE_WORD" || tok.Kind == "ATTRIBUTE_KEY" {
			got = append(got, tok.Kind+" "+tok.Text)
		}
	}
	if len(got) != len(want) {
		t.Fatal(got)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatal(i, got)
		}
	}
}

func hasToken(tokens []Token, kind, text string) bool {
	for _, tok := range tokens {
		if tok.Kind == kind && tok.Text == text {
			return true
		}
	}
	return false
}

func TestTextualRelationshipOperatorsDoNotSplitIdentifiers(t *testing.T) {
	tokens := Lex([]byte("TOP to optionally to to_customer to9 today"), nil)
	var got []string
	for _, tok := range tokens {
		got = append(got, tok.Kind+" "+tok.Text)
	}
	want := []string{
		"UNICODE_TEXT TOP",
		"IDENTIFYING to",
		"NON_IDENTIFYING optionally to",
		"UNICODE_TEXT to_customer",
		"UNICODE_TEXT to9",
		"UNICODE_TEXT today",
		"EOF ",
	}
	if len(got) != len(want) {
		t.Fatal(got)
	}
	for i := range want {
		if got[i] != want[i] {
			t.Fatal(i, got)
		}
	}
	if tokens[0].Span != (source.Span{Start: 0, End: 3}) {
		t.Fatal(tokens[0])
	}
}
