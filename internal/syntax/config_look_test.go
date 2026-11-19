package syntax

import "testing"

func readLook(t *testing.T, text string) (Look, int) {
	t.Helper()
	value, ds := ParseConfigYAML([]byte(text), 0, len(text))
	if len(ds) != 0 {
		t.Fatalf("%q: %v", text, ds)
	}
	look, found := ReadLook(value)
	return look, len(found)
}

func TestReadLookValues(t *testing.T) {
	for _, c := range []struct {
		text string
		want Look
	}{
		{"look: neo\n", Look{Value: "neo", HasValue: true}},
		{"look: \"handDrawn\"\nhandDrawnSeed: 7\n", Look{Value: "handDrawn", HasValue: true, Seed: 7, HasSeed: true}},
		{"handDrawnSeed: 4294967295\n", Look{Seed: 4294967295, HasSeed: true}},
		{"handDrawnSeed: +5\n", Look{Seed: 5, HasSeed: true}},
		{"handDrawnSeed: 0\n", Look{HasSeed: true}},
		{"look: other\n", Look{Value: "other", HasValue: true}},
	} {
		if got, errs := readLook(t, c.text); got != c.want || errs != 0 {
			t.Errorf("%q = %+v with %d diagnostics, want %+v", c.text, got, errs, c.want)
		}
	}
}

func TestReadLookRejectsBadSeeds(t *testing.T) {
	for _, text := range []string{
		"handDrawnSeed: 4294967296\n", "handDrawnSeed: -1\n", "handDrawnSeed: -0\n", "handDrawnSeed: 1.5\n",
		"handDrawnSeed: abc\n", "handDrawnSeed: true\n", "handDrawnSeed:\n", "handDrawnSeed: [1]\n", "handDrawnSeed: {a: 1}\n",
		"handDrawnSeed: 99999999999999999999\n",
	} {
		if got, errs := readLook(t, text); got != (Look{}) || errs != 1 {
			t.Errorf("%q = %+v with %d diagnostics", text, got, errs)
		}
	}
}

func TestReadLookDiagnosticShape(t *testing.T) {
	text := "look: neo\nhandDrawnSeed: abc\n"
	value, _ := ParseConfigYAML([]byte(text), 0, len(text))
	_, ds := ReadLook(value)
	if len(ds) != 1 {
		t.Fatal(ds)
	}
	d := ds[0]
	if d.Code != "config/malformed" || d.Severity.String() != "error" || d.Message != "invalid config value abc for handDrawnSeed" || d.Help != "Write a value that the config key accepts." {
		t.Errorf("%+v", d)
	}
	if text[d.Span.Start:d.Span.End] != "handDrawnSeed" {
		t.Errorf("span covers %q, want the key", text[d.Span.Start:d.Span.End])
	}
	for _, c := range []struct{ text, shown string }{{"handDrawnSeed: true\n", "true"}, {"handDrawnSeed:\n", "null"}, {"handDrawnSeed: [1]\n", "[...]"}, {"handDrawnSeed: {a: 1}\n", "{...}"}} {
		v, _ := ParseConfigYAML([]byte(c.text), 0, len(c.text))
		if _, ds := ReadLook(v); len(ds) != 1 || ds[0].Message != "invalid config value "+c.shown+" for handDrawnSeed" {
			t.Errorf("%q: %v", c.text, ds)
		}
	}
}

func TestReadLookLaterLayersWin(t *testing.T) {
	parse := func(text string) ConfigValue {
		v, _ := ParseConfigYAML([]byte(text), 0, len(text))
		return v
	}
	look, ds := ReadLook(parse("look: neo\nhandDrawnSeed: 1\n"), parse("look: handDrawn\n"), parse("handDrawnSeed: 9\n"), ConfigValue{})
	if len(ds) != 0 || look.Value != "handDrawn" || look.Seed != 9 {
		t.Errorf("%+v %v", look, ds)
	}
}

func TestLookOverlayKeepsBaseAndReportsOnlyNewErrors(t *testing.T) {
	parse := func(text string) ConfigValue {
		v, _ := ParseConfigYAML([]byte(text), 0, len(text))
		return v
	}
	base, ds := ReadLook(parse("look: neo\nhandDrawnSeed: 3\n"))
	if len(ds) != 0 {
		t.Fatal(ds)
	}
	got, ds := base.Overlay(ConfigValue{})
	if len(ds) != 0 || got != base {
		t.Errorf("empty overlay changed the base: %+v %v", got, ds)
	}
	got, ds = base.Overlay(parse("look: handDrawn\n"))
	if len(ds) != 0 || got.Value != "handDrawn" || got.Seed != 3 {
		t.Errorf("look overlay: %+v %v", got, ds)
	}
	got, ds = base.Overlay(parse("handDrawnSeed: -3\n"))
	if len(ds) != 1 || got != base {
		t.Errorf("bad seed overlay: %+v %v", got, ds)
	}
}
