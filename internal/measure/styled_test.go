package measure

import (
	"math/big"
	"reflect"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

func TestStyledCombinedWeightRounding(t *testing.T) {
	metric := ForRole(RoleLabel)
	for _, family := range []bool{false, true} {
		metric.FontFamily = family
		want := mixedWeightRationalWidth(t)
		if family {
			want = want * 108 / 100
		}
		lines, err := StyledLines("*A* **A**", 12800, metric)
		if err != nil {
			t.Fatal(err)
		}
		if len(lines) != 1 || lines[0].Text != "A A" || int64(lines[0].Width) != want {
			t.Fatalf("family %v: got %+v, want rendered A A width %d", family, lines, want)
		}
	}
}

func mixedWeightRationalWidth(t *testing.T) int64 {
	t.Helper()
	sum := new(big.Rat)
	for _, glyph := range []struct {
		weight uint8
		cp     rune
	}{{0, 'A'}, {1, ' '}, {1, 'A'}} {
		found := false
		for _, row := range gen.Advances {
			if row.Weight == glyph.weight && rune(row.CP) == glyph.cp {
				sum.Add(sum, new(big.Rat).SetFrac64(int64(row.Units)*14*64, int64(gen.AdvancesUpem[glyph.weight])))
				found = true
				break
			}
		}
		if !found {
			t.Fatalf("font row missing for %q", glyph.cp)
		}
	}
	quotient, remainder := new(big.Int), new(big.Int)
	quotient.QuoRem(sum.Num(), sum.Denom(), remainder)
	if remainder.Sign() != 0 {
		quotient.Add(quotient, big.NewInt(1))
	}
	return quotient.Int64()
}

func TestStyledCrossSpanGraphemes(t *testing.T) {
	for _, test := range []struct {
		source string
		runs   []StyledRun
		text   string
		width  int32
	}{
		{"**👩**\u200d*💻*x", []StyledRun{{Text: "👩", Bold: true}, {Text: "\u200d"}, {Text: "💻", Italic: true}}, "👩\u200d💻", 2},
		{"**☹***️*x", []StyledRun{{Text: "☹", Bold: true}, {Text: "️", Italic: true}}, "☹️", 2},
		{"**a***́*x", []StyledRun{{Text: "a", Bold: true}, {Text: "́", Italic: true}}, "á", 1},
	} {
		lines, err := StyledLines(test.source, 1, CellMetric())
		if err != nil {
			t.Fatal(err)
		}
		if len(lines) != 2 || lines[0].Text != test.text || lines[0].Width != test.width || lines[1].Text != "x" {
			t.Fatalf("%q: got %+v", test.source, lines)
		}
		runs := lines[0].Runs
		for i := range runs {
			runs[i].Width = 0
		}
		if !reflect.DeepEqual(runs, test.runs) {
			t.Fatalf("%q: got flags %+v, want %+v", test.source, runs, test.runs)
		}
	}
}

func TestStyledLiteralEscapes(t *testing.T) {
	for _, test := range []struct{ source, rendered string }{
		{`a_b_c **unclosed`, `a_b_c **unclosed`},
		{`\*x\* \_ \\ \$ \a`, `*x* _ \ $ \a`},
		{`$$x_**y**$$ &amp; <em>x</em>`, `$$x_**y**$$ &amp; <em>x</em>`},
		{"a_²_b", "a_²_b"},
		{"a_\u0345_b", "a_\u0345_b"},
		{"a_ⓐ_b", "a_ⓐ_b"},
		{"a_\u0558_b", "a_\u0558_b"},
		{"*a\nb*", "*a�b*"},
		{"**a\nb**", "**a�b**"},
		{"**a\rb**", "**a�b**"},
		{"**a\r\nb**", "**a��b**"},
	} {
		lines, err := StyledLines(test.source, 1000, CellMetric())
		if err != nil {
			t.Fatal(err)
		}
		wantWidth, err := CellWidth(test.rendered)
		if err != nil {
			t.Fatal(err)
		}
		if len(lines) != 1 || lines[0].Text != test.rendered || lines[0].Width != wantWidth {
			t.Fatalf("%q: got %+v, want %q width %d", test.source, lines, test.rendered, wantWidth)
		}
		for _, run := range lines[0].Runs {
			if run.Bold || run.Italic {
				t.Fatalf("%q: unexpected style %+v", test.source, run)
			}
		}
	}
}

func TestStyledForcedBreakBoundaries(t *testing.T) {
	lines, err := StyledLines("<BR>**a**<bR/>*b*<Br /><br>", 100, CellMetric())
	if err != nil {
		t.Fatal(err)
	}
	var texts []string
	for _, line := range lines {
		texts = append(texts, line.Text)
	}
	if !reflect.DeepEqual(texts, []string{"", "a", "b", ""}) {
		t.Fatalf("got forced lines %q", texts)
	}
	width, err := StyledWidth("**ab**<BR />*c*", CellMetric())
	if err != nil || width != 2 {
		t.Fatalf("got forced width %d, %v", width, err)
	}
}

func TestStyledControlBoundaries(t *testing.T) {
	for _, test := range []struct {
		source string
		target int32
		want   []StyledLine
	}{
		{"**a**\n*b*", 100, []StyledLine{{Text: "a�b", Width: 3, Runs: []StyledRun{{Text: "a", Bold: true}, {Text: "�"}, {Text: "b", Italic: true}}}}},
		{"**a**\x00*́*x", 1, []StyledLine{
			{Text: "a", Width: 1, Runs: []StyledRun{{Text: "a", Bold: true}}},
			{Text: "�́", Width: 1, Runs: []StyledRun{{Text: "�"}, {Text: "́", Italic: true}}},
			{Text: "x", Width: 1, Runs: []StyledRun{{Text: "x"}}},
		}},
		{"\x00\x1f\x7f\u009f", 2, []StyledLine{
			{Text: "��", Width: 2, Runs: []StyledRun{{Text: "��"}}},
			{Text: "��", Width: 2, Runs: []StyledRun{{Text: "��"}}},
		}},
		{"\u0020\u007e\u00a0", 100, []StyledLine{{Text: " ~\u00a0", Width: 3, Runs: []StyledRun{{Text: " ~\u00a0"}}}}},
	} {
		lines, err := StyledLines(test.source, test.target, CellMetric())
		if err != nil {
			t.Fatal(err)
		}
		for i := range lines {
			for j := range lines[i].Runs {
				lines[i].Runs[j].Width = 0
			}
		}
		if !reflect.DeepEqual(lines, test.want) {
			t.Fatalf("%q: got %+v, want %+v", test.source, lines, test.want)
		}
	}
}

func TestStyledVectorControlBoundaries(t *testing.T) {
	for _, source := range []string{"**a\nb**", "**a\rb**", "**a\r\nb**"} {
		lines, err := StyledLines(source, 10000, ForRole(RoleLabel))
		if err != nil {
			t.Fatal(err)
		}
		if len(lines) != 1 || lines[0].Text != source {
			t.Fatalf("%q: vector text changed: %+v", source, lines)
		}
		for _, run := range lines[0].Runs {
			if run.Bold || run.Italic {
				t.Fatalf("%q: unexpected vector style %+v", source, run)
			}
		}
	}
}
