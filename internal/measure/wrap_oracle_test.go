package measure

import (
	"reflect"
	"testing"
)

func TestGreedyWrapOracle(t *testing.T) {
	cases := []struct {
		input  string
		target int32
		want   []Line
	}{
		{"alpha beta-gamma 日本語テキスト", 8, []Line{{"alpha", " ", 5}, {"beta-", "", 5}, {"gamma 日", "", 8}, {"本", "", 2}, {"語テキス", "", 8}, {"ト", "", 2}}},
		{"a  b ", 3, []Line{{"a", "  ", 1}, {"b", " ", 1}}},
		{"a<br>b", 8, []Line{{"a", "<br>", 1}, {"b", "", 1}}},
		{"日本", 1, []Line{{"日", "", 2}, {"本", "", 2}}},
	}
	for _, c := range cases {
		got, err := Wrap(c.input, c.target, CellMetric())
		if err != nil || !reflect.DeepEqual(got, c.want) {
			t.Fatalf("Wrap(%q)=%+v %v want %+v", c.input, got, err, c.want)
		}
	}
}
