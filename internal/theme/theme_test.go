package theme_test

import (
	"errors"
	"math"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/gen"
	"github.com/gosuda/elegant-mermaid/internal/theme"
)

func colour(t *testing.T, s string) theme.Colour {
	t.Helper()
	c, err := theme.ParseHex(s)
	if err != nil {
		t.Fatal(err)
	}
	return c
}

func luminance(c theme.Colour) float64 {
	linear := func(v uint8) float64 {
		u := float64(v) / 255
		if u <= .04045 {
			return u / 12.92
		}
		return math.Pow((u+.055)/1.055, 2.4)
	}
	return .2126*linear(c.R) + .7152*linear(c.G) + .0722*linear(c.B)
}
func ratio(a, b theme.Colour) float64 {
	x, y := luminance(a), luminance(b)
	return (math.Max(x, y) + .05) / (math.Min(x, y) + .05)
}

func TestBuiltInThemeContrast(t *testing.T) {
	names := []string{"elegant-light", "elegant-dark", "github-light", "github-dark", "catppuccin-latte", "catppuccin-mocha", "nord", "solarized-light", "solarized-dark"}
	expected := map[string][10]float64{
		"elegant-light": {15.98, 15.58, 5.79, 5.64, 3.69, 3.59, 3.21, 3.13, 3.18, 3.10},
		"elegant-dark":  {16.24, 15.15, 9.05, 8.44, 4.44, 4.14, 3.68, 3.43, 5.77, 5.38},
	}
	for _, name := range names {
		th, err := theme.Resolve(name)
		if err != nil {
			t.Fatal(err)
		}
		for i, token := range []theme.Token{theme.Foreground, theme.Muted, theme.Line, theme.Border, theme.Accent} {
			threshold := int32(30)
			if i < 2 {
				threshold = 45
			}
			for j, surface := range []theme.Token{theme.Background, theme.Surface} {
				checkContrastPair(t, th, token, surface, threshold)
				if values, ok := expected[name]; ok {
					checkRatio(t, th, token, surface, values[2*i+j])
				}
			}
		}
	}
}

func TestColourArithmetic(t *testing.T) {
	cases := []struct {
		hex string
		h   theme.HSL
	}{
		{"#000000", theme.HSL{H: 0, S: 0, L: 0}}, {"#ffffff", theme.HSL{H: 0, S: 0, L: 100}},
		{"#808080", theme.HSL{H: 0, S: 0, L: 50}}, {"#ff0000", theme.HSL{H: 0, S: 100, L: 50}},
		{"#00ff00", theme.HSL{H: 120, S: 100, L: 50}}, {"#0000ff", theme.HSL{H: 240, S: 100, L: 50}},
		{"#ffff00", theme.HSL{H: 60, S: 100, L: 50}}, {"#00ffff", theme.HSL{H: 180, S: 100, L: 50}},
		{"#ff00ff", theme.HSL{H: 300, S: 100, L: 50}}, {"#404040", theme.HSL{H: 0, S: 0, L: 25}},
		{"#bfbfbf", theme.HSL{H: 0, S: 0, L: 75}}, {"#8b8d98", theme.HSL{H: 231, S: 6, L: 57}},
	}
	for _, tc := range cases {
		c := colour(t, tc.hex)
		if c.HSL() != tc.h {
			t.Errorf("%s HSL %v want %v", tc.hex, c.HSL(), tc.h)
		}
		if theme.Invert(theme.Invert(c)) != c {
			t.Fatal("invert identity")
		}
	}
}

func TestHexAndAdjust(t *testing.T) {
	if colour(t, "#aBc").Hex() != "#aabbcc" {
		t.Fatal("short hex")
	}
	for _, bad := range []string{"", "fff", "#12", "#1234", "#ggg", "#12345z"} {
		_, err := theme.ParseHex(bad)
		if !errors.Is(err, theme.ErrBadColour) {
			t.Fatalf("accepted %q", bad)
		}
	}
	c := colour(t, "#3366cc")
	if theme.Adjust(c, theme.Delta{H: -560}) != theme.Adjust(c, theme.Delta{H: 160}) {
		t.Fatal("negative hue wrap")
	}
	if !theme.IsDark(colour(t, "#000")) || theme.IsDark(colour(t, "#fff")) || !theme.IsDark(colour(t, "#777")) {
		t.Fatal("dark threshold")
	}
	t.Logf("twin HSL=%v darken=%s lighten=%s adjust=%s invert=%s borderDark=%s borderLight=%s isDark777=%v Y=%d", colour(t, "#8b8d98").HSL(), theme.Darken(c, 10).Hex(), theme.Lighten(c, 10).Hex(), theme.Adjust(c, theme.Delta{H: -200, S: 5, L: -3}).Hex(), theme.Invert(colour(t, "#123456")).Hex(), theme.MkBorderDark(c).Hex(), theme.MkBorderLight(c).Hex(), theme.IsDark(colour(t, "#777")), theme.Luminance(colour(t, "#8b8d98")))
}

func TestGeneratedChoices(t *testing.T) {
	for _, row := range gen.StrokeOk {
		th, err := theme.Resolve(row.Theme)
		if err != nil {
			t.Fatal(err)
		}
		token := namedToken(row.Token)
		want := token
		if row.OK == 0 {
			want = theme.Line
		}
		if th.Stroke(token) != want {
			t.Fatalf("%s %s fallback", row.Theme, row.Token)
		}
	}
	for _, row := range gen.SeriesText {
		th, err := theme.Resolve(row.Theme)
		if err != nil {
			t.Fatal(err)
		}
		if th.SeriesText(row.Series) != theme.TextChoice(row.Choice) {
			t.Fatal("series choice")
		}
		choice := independentChoice(th, row.Series)
		if th.SeriesText(row.Series) != choice {
			t.Fatalf("%s series %d independent choice %v want %v", row.Theme, row.Series, th.SeriesText(row.Series), choice)
		}
	}
	_, err := theme.Resolve("missing")
	if _, ok := errors.AsType[*theme.UnknownThemeError](err); !ok {
		t.Fatal("unknown theme error")
	}
}

func TestColourReference(t *testing.T) {
	state := uint32(1)
	worst := 0.0
	for range 2000 {
		state ^= state << 13
		state ^= state >> 17
		state ^= state << 5
		c := theme.Colour{R: uint8(state), G: uint8(state >> 8), B: uint8(state >> 16)}
		h := c.HSL()
		checkHSLReference(t, c, h)
		reference := floatRGB(h)
		back := theme.FromHSL(h)
		for i, v := range []uint8{back.R, back.G, back.B} {
			if math.Abs(float64(v)-reference[i]) > 2 {
				t.Fatalf("HSL reference %v %v", back, reference)
			}
		}
		for i, v := range []uint8{c.R, c.G, c.B} {
			actual := []uint8{back.R, back.G, back.B}[i]
			worst = math.Max(worst, math.Abs(float64(v)-float64(actual)))
		}
		if math.Abs(float64(theme.Luminance(c))/65535-luminance(c)) > .00003 {
			t.Fatal("luminance reference")
		}
		checkContrastReference(t, c)
	}
	t.Logf("2000-draw maximum round-trip error %.0f", worst)
	if worst > 5 {
		t.Fatal("round-trip bound")
	}
}

func floatRGB(h theme.HSL) [3]float64 {
	l, s := float64(h.L)/100, float64(h.S)/100
	c := (1 - math.Abs(2*l-1)) * s
	x := c * (1 - math.Abs(math.Mod(float64(h.H)/60, 2)-1))
	parts := [6][3]float64{{c, x, 0}, {x, c, 0}, {0, c, x}, {0, x, c}, {x, 0, c}, {c, 0, x}}
	out := parts[h.H/60]
	for i := range out {
		out[i] = (out[i] + l - c/2) * 255
	}
	return out
}

func checkHSLReference(t *testing.T, c theme.Colour, h theme.HSL) {
	t.Helper()
	r, g, b := float64(c.R)/255, float64(c.G)/255, float64(c.B)/255
	hi, lo := math.Max(r, math.Max(g, b)), math.Min(r, math.Min(g, b))
	d := hi - lo
	l := (hi + lo) / 2
	s, hue := 0.0, 0.0
	if d != 0 {
		s = d / (1 - math.Abs(2*l-1))
		switch hi {
		case r:
			hue = 60 * math.Mod((g-b)/d+6, 6)
		case g:
			hue = 60 * ((b-r)/d + 2)
		case b:
			hue = 60 * ((r-g)/d + 4)
		}
	}
	hueError := math.Abs(float64(h.H) - hue)
	hueError = math.Min(hueError, 360-hueError)
	if hueError > .500001 || math.Abs(float64(h.S)-100*s) > .500001 || math.Abs(float64(h.L)-100*l) > .500001 {
		t.Fatalf("RGB reference %v -> %v vs %f %f %f", c, h, hue, 100*s, 100*l)
	}
}

func namedToken(name string) theme.Token {
	for token := theme.Background; token <= theme.Success; token++ {
		if token.String() == name {
			return token
		}
	}
	return theme.Error
}

func independentChoice(th theme.Theme, series uint8) theme.TextChoice {
	fill := th.Colour(theme.Series0 + theme.Token(series))
	fg, bg := ratio(fill, th.Colour(theme.Foreground)), ratio(fill, th.Colour(theme.Background))
	if fg >= 4.5 && fg >= bg {
		return theme.TextForeground
	}
	if bg >= 4.5 && bg > fg {
		return theme.TextBackground
	}
	return theme.TextPlate
}

func checkContrastPair(t *testing.T, th theme.Theme, token, surface theme.Token, threshold int32) {
	t.Helper()
	a, b := th.Colour(token), th.Colour(surface)
	r := ratio(a, b)
	if r < float64(threshold)/10 || !theme.Contrast(a, b, threshold) {
		t.Fatalf("%s %s contrast %f", th.Name(), token, r)
	}
}

func checkRatio(t *testing.T, th theme.Theme, token, surface theme.Token, want float64) {
	t.Helper()
	r := math.Floor(ratio(th.Colour(token), th.Colour(surface))*100) / 100
	if r != want {
		t.Errorf("%s %s ratio %.2f want %.2f", th.Name(), token, r, want)
	}
}

func checkContrastReference(t *testing.T, c theme.Colour) {
	t.Helper()
	b := theme.Invert(c)
	for _, threshold := range []int32{30, 45} {
		r := ratio(c, b)
		if math.Abs(r-float64(threshold)/10) > .01 && theme.Contrast(c, b, threshold) != (r >= float64(threshold)/10) {
			t.Fatal("contrast verdict")
		}
	}
}
