package cli

import (
	"path/filepath"
	"testing"
)

func TestRenderNumericFlagsUseDecimal(t *testing.T) {
	for _, value := range []string{"8", "08", "008", "+8"} {
		out, stderr, code := invoke(t, cleanSource, "render", "-e", "text", "-s", value)
		if code != 0 || out == "" || stderr != "" {
			t.Errorf("-s %s: exit=%d stdout=%q stderr=%q", value, code, out, stderr)
		}
	}
	for _, tc := range []struct{ flag, value, accepted string }{
		{"-s", "010", "1..8"},
		{"-s", "+9", "1..8"},
		{"-s", "09", "1..8"},
		{"-s", "-00", "1..8"},
		{"-s", "-0=invalid", "1..8"},
		{"-s", "0x2", "1..8"},
		{"-s", "0b10", "1..8"},
		{"-s", "0o2", "1..8"},
		{"--width", "0x10", "non-negative integers"},
		{"--width", "0b10", "non-negative integers"},
		{"--width", "0o10", "non-negative integers"},
		{"--width", "1_0", "non-negative integers"},
		{"--width", "-01", "non-negative integers"},
		{"--width", "+2147483648", "non-negative integers"},
		{"--width", "-0=invalid", "non-negative integers"},
	} {
		want := "invalid value " + tc.value + " for " + tc.flag + "; expected one of: " + tc.accepted + "\n"
		expectInvocation(t, cleanSource, []string{"render", "-e", "text", tc.flag, tc.value}, "", want, 2)
		expectInvocation(t, cleanSource, []string{"render", "-e", "text", tc.flag, tc.value, tc.flag, "2"}, "", want, 2)
	}
	for _, value := range []string{"010", "0010", "+10"} {
		options, _, err := commandFlags("render", []string{"--width=" + value})
		if err != nil || options.width != 10 {
			t.Errorf("--width=%s: width=%d err=%v", value, options.width, err)
		}
	}
}

func TestRenderNumericFlagDefaultsAndZero(t *testing.T) {
	for _, args := range [][]string{nil, {"--width", "-0"}, {"--width=-00"}} {
		options, _, err := commandFlags("render", args)
		if err != nil || options.width != 0 || options.scale != 2 {
			t.Fatalf("%q: width=%d scale=%d err=%v", args, options.width, options.scale, err)
		}
	}
}

var flagSpellings = [][][]string{
	{
		{"view", "good.mmd", "--script", "ok.script", "-t", "elegant-dark", "--color", "never", "--graphics", "cells"},
		{"view", "good.mmd", "-script=ok.script", "-t=elegant-dark", "-color=never", "-graphics=cells"},
		{"view", "good.mmd", "--script=ok.script", "--t=elegant-dark", "--color=never", "--graphics=cells"},
		{"view", "--script", "ok.script", "-t=elegant-dark", "good.mmd", "-color", "never", "--graphics=cells"},
		{"view", "-script", "ok.script", "--t", "elegant-dark", "-color=never", "-graphics", "cells", "--", "good.mmd"},
	},
	{
		{"render", "good.mmd", "-e", "text", "--charset", "ascii", "--width", "12", "--color", "never"},
		{"render", "good.mmd", "-e=text", "-charset=ascii", "-width=12", "-color=never"},
		{"render", "good.mmd", "--e=text", "--charset=ascii", "--width=12", "--color=never"},
		{"render", "-width", "12", "--e", "text", "good.mmd", "-charset", "ascii", "--color", "never"},
	},
	{
		{"check", "good.mmd", "--output-format", "json", "--color", "never"},
		{"check", "good.mmd", "-output-format=json", "-color=never"},
		{"check", "-output-format", "json", "good.mmd", "--color=never"},
	},
	{
		{"lint", "good.mmd", "--output-format", "json", "--no-config", "--deny-warnings"},
		{"lint", "good.mmd", "-output-format=json", "-no-config=true", "-deny-warnings=1"},
		{"lint", "good.mmd", "--output-format=json", "--no-config=T", "--deny-warnings=TRUE"},
		{"lint", "--no-config", "-output-format", "json", "good.mmd", "-deny-warnings"},
	},
	{
		{"layout", "good.mmd", "--profile", "cell", "--stage", "model"},
		{"layout", "good.mmd", "-profile=cell", "-stage=model"},
		{"layout", "--profile=cell", "good.mmd", "--stage=model"},
		{"layout", "-profile", "cell", "--stage", "model", "--", "good.mmd"},
	},
	{
		{"layout", "--metrics", "--dump", "good.dump"},
		{"layout", "-metrics=true", "-dump=good.dump"},
		{"layout", "--metrics=1", "--dump=good.dump"},
		{"layout", "-dump", "good.dump", "--metrics"},
	},
	{
		{"explain", "flowchart/unexpected-token", "--output-format", "json"},
		{"explain", "-output-format=json", "flowchart/unexpected-token"},
		{"explain", "--output-format=json", "--", "flowchart/unexpected-token"},
	},
}

var flagSpellingFailures = []struct {
	args   []string
	stderr string
}{
	{[]string{"view", "good.mmd", "---t", "elegant-dark"}, "unknown flag ---t; run emd view --help\n"},
	{[]string{"view", "good.mmd", "---script=ok.script"}, "unknown flag ---script=ok.script; run emd view --help\n"},
	{[]string{"render", "good.mmd", "---width=5"}, "unknown flag ---width=5; run emd render --help\n"},
	{[]string{"render", "good.mmd", "---e", "svg"}, "unknown flag ---e; run emd render --help\n"},
	{[]string{"check", "good.mmd", "---color"}, "unknown flag ---color; run emd check --help\n"},
	{[]string{"lint", "good.mmd", "---fix"}, "unknown flag ---fix; run emd lint --help\n"},
	{[]string{"layout", "good.mmd", "---metrics"}, "unknown flag ---metrics; run emd layout --help\n"},
	{[]string{"explain", "flowchart/unexpected-token", "---output-format=json"}, "unknown flag ---output-format=json; run emd explain --help\n"},
	{[]string{"layout", "good.mmd", "-x"}, "unknown flag -x; run emd layout --help\n"},
	{[]string{"view", "good.mmd", "--t"}, "missing value for --t\n"},
	{[]string{"view", "good.mmd", "-script"}, "missing value for -script\n"},
	{[]string{"layout", "good.mmd", "-profile"}, "missing value for -profile\n"},
	{[]string{"explain", "--output-format"}, "missing value for --output-format\n"},
	{[]string{"view", "good.mmd", "--script="}, "cannot read : no such file or directory\n"},
	{[]string{"view", "good.mmd", "--script", ""}, "cannot read : no such file or directory\n"},
	{[]string{"lint", "good.mmd", "--fix=maybe"}, "invalid value maybe for --fix; expected one of: true, false\n"},
	{[]string{"layout", "good.mmd", "-metrics=maybe"}, "invalid value maybe for --metrics; expected one of: true, false\n"},
	{[]string{"layout", "good.mmd", "-profile=bogus"}, "invalid value bogus for --profile; expected one of: vector, cell\n"},
	{[]string{"layout", "good.mmd", "--stage=bogus"}, "invalid value bogus for --stage; expected one of: model, layout\n"},
}

func TestFlagSpellings(t *testing.T) {
	dir := t.TempDir()
	writeViewInput(t, filepath.Join(dir, "good.mmd"), "flowchart LR\n A[alpha] --> B\n")
	writeViewInput(t, filepath.Join(dir, "ok.script"), "settle\n")
	t.Chdir(dir)
	dump, _, _ := invoke(t, "", "layout", "good.mmd")
	writeViewInput(t, filepath.Join(dir, "good.dump"), dump)
	for _, group := range flagSpellings {
		requireSpellingsAgree(t, group)
	}
	for _, c := range flagSpellingFailures {
		out, stderr, code := invoke(t, "", c.args...)
		if out != "" || stderr != c.stderr || code != 2 {
			t.Errorf("%q: stdout=%q stderr=%q exit=%d; want stderr=%q exit=2", c.args, out, stderr, code, c.stderr)
		}
	}
}

func requireSpellingsAgree(t *testing.T, group [][]string) {
	t.Helper()
	wantOut, wantErr, wantCode := invoke(t, "", group[0]...)
	if wantCode != 0 || wantOut == "" {
		t.Fatalf("%q: stdout=%q stderr=%q exit=%d; want output and exit 0", group[0], wantOut, wantErr, wantCode)
	}
	for _, args := range group[1:] {
		out, stderr, code := invoke(t, "", args...)
		if out != wantOut || stderr != wantErr || code != wantCode {
			t.Errorf("%q: stdout=%q stderr=%q exit=%d; want the result of %q", args, out, stderr, code, group[0])
		}
	}
}
