package measure

import (
	"reflect"
	"slices"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
)

func TestSegmentRules(t *testing.T) {
	cases := []struct {
		input string
		want  []string
	}{
		{"", nil},
		{"abc", []string{"a", "b", "c"}},
		{"\r\n", []string{"\r\n"}},
		{"a\rb", []string{"a", "\r", "b"}},
		{"a\nb", []string{"a", "\n", "b"}},
		{"a\x00b", []string{"a", "\x00", "b"}},
		{"ᄀ각", []string{"ᄀ각"}},
		{"가ᅡᆨ", []string{"가ᅡᆨ"}},
		{"각ᆨ", []string{"각ᆨ"}},
		{"á", []string{"á"}},
		{"a\u200d", []string{"a\u200d"}},
		{"कः", []string{"कः"}},
		{"\u0600a", []string{"\u0600a"}},
		{"\u0600\u0600a", []string{"\u0600\u0600a"}},
		{"क्क", []string{"क्क"}},
		{"क्\u0301क", []string{"क्\u0301क"}},
		{"👩\u200d💻", []string{"👩\u200d💻"}},
		{"👩́\u200d💻", []string{"👩́\u200d💻"}},
		{"🇦🇧🇨🇩🇪", []string{"🇦🇧", "🇨🇩", "🇪"}},
		{"🇦🇧a🇨🇩", []string{"🇦🇧", "a", "🇨🇩"}},
	}
	base := len(cases)
	for i := 1; i < base; i++ {
		c := cases[i]
		prefix := append([]string{"\x00"}, c.want...)
		suffix := append(slices.Clone(c.want), "\x00")
		cases = append(cases, struct {
			input string
			want  []string
		}{"\x00" + c.input, prefix})
		cases = append(cases, struct {
			input string
			want  []string
		}{c.input + "\x00", suffix})
	}
	for _, c := range cases {
		got := Segment(c.input)
		var texts []string
		for _, cluster := range got {
			texts = append(texts, cluster.Text)
		}
		if !reflect.DeepEqual(texts, c.want) {
			t.Errorf("Segment(%q)=%q want %q", c.input, texts, c.want)
		}
	}
}

func TestWidths(t *testing.T) {
	for _, c := range []struct {
		s    string
		want int32
	}{{"", 0}, {"Start", 5}, {"日本語", 6}, {"☹️", 2}, {"1️⃣", 2}, {"́", 0}, {"👩‍💻", 2}} {
		got, err := CellWidth(c.s)
		if err != nil || got != c.want {
			t.Errorf("CellWidth(%q)=%d,%v want %d", c.s, got, err, c.want)
		}
	}
	for _, s := range []string{"", "Start", "Choice", "yes", "日本語", "abc", "0123456789"} {
		sum := naiveAdvanceSum(s)
		want := int32((sum*896 + 2047) / 2048)
		got, err := RoleLabel.Width(s)
		if err != nil || got != want {
			t.Errorf("Width(%q)=%d,%v want %d", s, got, err, want)
		}
	}
}

func TestRandomWrapProperties(t *testing.T) {
	alphabet := []rune("ab -日本語́👩\u200d💻🇦🇧")
	for seed := uint32(1); seed <= 2000; seed++ {
		state := seed
		var b strings.Builder
		for range 1 + int(seed%50) {
			state ^= state << 13
			state ^= state >> 17
			state ^= state << 5
			b.WriteRune(alphabet[int(state)%len(alphabet)])
		}
		input := b.String()
		clusters := Segment(input)
		var joined strings.Builder
		boundaries := map[int]bool{0: true}
		for _, c := range clusters {
			joined.WriteString(c.Text)
			boundaries[joined.Len()] = true
		}
		if joined.String() != input {
			t.Fatal("segmentation loses text")
		}
		checkWrapped(t, input, int32(1+seed%12), boundaries)
	}
}

func TestParityValues(t *testing.T) {
	for _, s := range []string{"Start", "Choice", "yes"} {
		w, err := RoleLabel.Width(s)
		if err != nil {
			t.Fatal(err)
		}
		t.Logf("label %s=%d", s, w)
	}
	s := "alpha beta-gamma 日本語テキスト"
	w, err := CellWidth(s)
	if err != nil {
		t.Fatal(err)
	}
	lines, err := Wrap(s, 8, CellMetric())
	if err != nil {
		t.Fatal(err)
	}
	t.Logf("cell width=%d wrap=%+v", w, lines)
}

func naiveAdvanceSum(s string) int64 {
	var sum int64
	for _, cp := range s {
		advance := int64(1229)
		if cp >= '日' {
			advance = 2048
		}
		for _, row := range gen.Advances {
			if row.Weight == 1 && row.CP == uint32(cp) {
				advance = int64(row.Units)
				break
			}
		}
		sum += advance
	}
	return sum
}

func checkWrapped(t *testing.T, input string, target int32, boundaries map[int]bool) {
	t.Helper()
	lines, err := Wrap(input, target, CellMetric())
	if err != nil {
		t.Fatal(err)
	}
	var joined strings.Builder
	for _, line := range lines {
		joined.WriteString(line.Text)
		if !boundaries[joined.Len()] {
			t.Fatal("split cluster")
		}
		joined.WriteString(line.Separator)
		if !boundaries[joined.Len()] {
			t.Fatal("split separator")
		}
		if line.Width > target && len(Segment(line.Text)) != 1 {
			t.Fatalf("overwide line %q", line.Text)
		}
	}
	if joined.String() != input {
		t.Fatalf("wrap loses %q", input)
	}
}
