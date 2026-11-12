package geom

import (
	"errors"
	"os/exec"
	"strings"
	"testing"
)

func TestParseCaseInt(t *testing.T) {
	ok := map[string]int64{
		"0": 0, "1": 1, "-1": -1, "2147483647": math32Max(), "-2147483648": math32Min(), "42": 42,
	}
	for in, want := range ok {
		got, valid := parseCaseInt(in)
		if !valid || got != want {
			t.Fatalf("parseCaseInt(%q)=%d,%v want %d", in, got, valid, want)
		}
	}
	bad := []string{"", "-0", "01", "00", "+1", "1a", "2147483648", "-2147483649", " 1", "1 ", "-", "--1"}
	for _, in := range bad {
		if _, valid := parseCaseInt(in); valid {
			t.Fatalf("parseCaseInt(%q) accepted", in)
		}
	}
}

func math32Max() int64 { return int64(I32Max) }

func math32Min() int64 { return int64(I32Min) }

func runEval(t *testing.T, input string) (string, error) {
	t.Helper()
	var sb strings.Builder
	err := Eval(strings.NewReader(input), &sb)
	return sb.String(), err
}

func TestEvalOperations(t *testing.T) {
	cases := []struct{ line, want string }{
		{"translate (1,2,3,4) 5 -6 -> (6,-4,3,4)", "(6,-4,3,4)"},
		{"inflate (0,0,2,2) -2 -> domain", "domain"},
		{"union (0,0,1,1) (5,5,2,2) -> (0,0,7,7)", "(0,0,7,7)"},
		{"intersects (0,0,2,2) (2,0,2,2) -> false", "false"},
		{"place_after X (0,0,3,3) 2 (4,5) -> (5,0,4,5)", "(5,0,4,5)"},
		{"compact Y 1 [(0,0,1,2),(0,1,1,2)] -> [(0,0,1,2),(0,3,1,2)]", "[(0,0,1,2),(0,3,1,2)]"},
		{"polyline_hits_rect [(0,0),(5,5)] (1,1,2,2) -> true", "true"},
		{"isqrt 99 -> 9", "9"},
		{"sin_q15 4096 -> 12540", "12540"},
		{"cos_q15 -1 -> 32768", "32768"},
		{"translate (2147483647,0,0,0) 1 0 -> overflow", "overflow"},
		{"translate (0,0,1,1) 5 -3 -> (5,-3,1,1)", "(5,-3,1,1)"},
		{"inflate (0,0,4,4) 1 -> (-1,-1,6,6)", "(-1,-1,6,6)"},
		{"union (0,0,2,2) (5,5,1,1) -> (0,0,6,6)", "(0,0,6,6)"},
		{"intersects (0,0,1,1) (2,2,1,1) -> false", "false"},
		{"intersects (0,0,4,4) (2,2,1,1) -> true", "true"},
		{"contains (0,0,10,10) (1,1,2,2) -> true", "true"},
		{"contains (0,0,10,10) (1,1,20,2) -> false", "false"},
		{"place_after X (0,0,2,2) 3 (4,1) -> (5,0,4,1)", "(5,0,4,1)"},
		{"place_after Y (0,0,2,2) 3 (4,1) -> (0,5,4,1)", "(0,5,4,1)"},
		{"compact X 2 [(0,0,2,1),(1,0,2,1)] -> [(0,0,2,1),(4,0,2,1)]", "[(0,0,2,1),(4,0,2,1)]"},
		{"compact Y 1 [] -> []", "[]"},
		{"segments_cross (0,0,4,0) (2,-1,2,1) -> true", "true"},
		{"segments_cross (0,0,4,0) (4,-1,4,1) -> false", "false"},
		{"is_orthogonal [(0,0),(3,0),(3,2)] -> true", "true"},
		{"is_orthogonal [(0,0),(1,1)] -> false", "false"},
		{"polyline_hits_rect [(0,0),(5,5)] (1,1,1,1) -> true", "true"},
		{"polyline_hits_rect [(0,0),(5,0)] (0,0,5,5) -> false", "false"},
		{"count_inversions [3,1,2] -> 2", "2"},
		{"count_inversions [] -> 0", "0"},
		{"isqrt 17 -> 4", "4"},
		{"isqrt 0 -> 0", "0"},
		{"sin_q15 16384 -> 32768", "32768"},
		{"sin_q15 -32768 -> 0", "0"},
		{"cos_q15 0 -> 32768", "32768"},
		{"translate (0,0,-1,1) 0 0 -> (0,0,0,0)", "domain"},
		{"translate (0,0,1,1) 2147483647 0 -> overflow", "overflow"},
		{"isqrt -1 -> 0", "domain"},
		{"compact Y 0 [(0,0,0,3),(0,1,0,1)] -> [(0,0,0,3),(0,3,0,1)]", "[(0,0,0,3),(0,3,0,1)]"},
	}
	for _, c := range cases {
		got, err := runEval(t, c.line+"\n")
		if err != nil {
			t.Fatalf("%q: %v", c.line, err)
		}
		if got != c.want+"\n" {
			t.Fatalf("%q: got %q want %q", c.line, got, c.want)
		}
	}
}

func TestEvalDeclaredResultIgnored(t *testing.T) {
	got, err := runEval(t, "isqrt 17 -> 999\n")
	if err != nil {
		t.Fatalf("%v", err)
	}
	if got != "4\n" {
		t.Fatalf("declared result must not drive evaluation: %q", got)
	}
}

func TestEvalErrors(t *testing.T) {
	bad := []string{
		"",
		"isqrt 17",
		"isqrt 17 ->",
		"isqrt -> 4",
		"unknown_op 1 -> 1",
		"isqrt 17 3 -> 4",
		"isqrt 3000000000 -> 4",
		"isqrt 017 -> 4",
		"isqrt 17 -> bogus",
		"place_after Z (0,0,1,1) 0 (1,1) -> (0,0,1,1)",
		"translate (0,0,1) 0 0 -> (0,0,1,1)",
		"translate (0,0,1,1) 0 -> (0,0,1,1)",
		"compact X 1 [1] -> []",
		"compact X 1 [(0,0,1,1),(1,1)] -> []",
	}
	for _, line := range bad {
		var sb strings.Builder
		err := Eval(strings.NewReader(line+"\n"), &sb)
		if ce, ok := errors.AsType[*CaseError](err); !ok || ce.Line != 1 {
			t.Fatalf("%q: got %v want case error line 1", line, err)
		}
	}
}

func TestEvalLineNumbers(t *testing.T) {
	input := "isqrt 4 -> 2\nisqrt 9 -> 3\nbroken\nisqrt 16 -> 4\n"
	var sb strings.Builder
	err := Eval(strings.NewReader(input), &sb)
	ce, ok := errors.AsType[*CaseError](err)
	if !ok || ce.Line != 3 {
		t.Fatalf("got %v, want case error on line 3", err)
	}
	if ce.Error() != "bad case line 3" {
		t.Fatalf("message %q", ce.Error())
	}
	if sb.String() != "2\n3\n" {
		t.Fatalf("output before the failure: %q", sb.String())
	}
}

func TestEvalEmptyInput(t *testing.T) {
	got, err := runEval(t, "")
	if err != nil {
		t.Fatalf("%v", err)
	}
	if got != "" {
		t.Fatalf("empty input produced %q", got)
	}
}

func TestEvalEmittedTokensFitResultGrammar(t *testing.T) {
	lines := []string{
		"translate (0,0,1,1) 2147483647 0 -> overflow",
		"translate (0,0,-1,1) 0 0 -> (0,0,0,0)",
		"inflate (0,0,4,4) -9 -> domain",
		"union (0,0,2,2) (5,5,1,1) -> (0,0,6,6)",
		"intersects (0,0,4,4) (2,2,1,1) -> true",
		"contains (0,0,1,1) (2,2,1,1) -> false",
		"place_after Y (0,0,2,2) 3 (4,1) -> (0,5,4,1)",
		"compact X 2 [(0,0,2,1),(1,0,2,1)] -> []",
		"compact X 0 [] -> []",
		"segments_cross (0,0,4,0) (2,-1,2,1) -> true",
		"is_orthogonal [] -> true",
		"is_orthogonal [(0,0),(1,1)] -> false",
		"polyline_hits_rect [] (0,0,1,1) -> false",
		"polyline_hits_rect [(0,0),(5,5)] (1,1,1,1) -> true",
		"count_inversions [5,4,3,2,1] -> 10",
		"count_inversions [] -> 0",
		"isqrt 100000 -> 316",
		"isqrt -5 -> 0",
		"sin_q15 -70000 -> 0",
		"cos_q15 12345 -> 0",
	}
	for _, line := range lines {
		token, ok := evalLine(line)
		if !ok {
			t.Fatalf("%q: line rejected", line)
		}
		token = strings.TrimSuffix(token, "\n")
		if !validResult(token) {
			t.Fatalf("%q: emitted token %q fails the result grammar", line, token)
		}
	}
}

func TestEvalGeneratedCases(t *testing.T) {
	cmd := exec.CommandContext(t.Context(), "go", "run", "../../tools/kernelgen")
	input, err := cmd.Output()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Count(string(input), "\n") != 14000 {
		t.Fatal("kernelgen must emit 14000 cases")
	}
	output, err := runEval(t, string(input))
	if err != nil {
		t.Fatal(err)
	}
	if strings.Count(output, "\n") != 14000 {
		t.Fatal("each generated case must produce one result")
	}
}

func TestEvalRequiresLineFeed(t *testing.T) {
	_, err := runEval(t, "isqrt 99 -> 9")
	if _, ok := errors.AsType[*CaseError](err); !ok {
		t.Fatalf("missing LF: %v", err)
	}
}
