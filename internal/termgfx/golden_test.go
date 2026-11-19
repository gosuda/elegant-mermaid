package termgfx_test

import (
	"bytes"
	"fmt"
	"image"
	"image/draw"
	"image/png"
	"os"
	"path/filepath"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
)

const goldenDir = "../../corpus/termgfx"

var goldenFixtures = []string{"tiny", "tall", "wide"}

type goldenEncoder struct {
	extension string
	encode    func(pngBytes []byte, pixels *image.NRGBA) ([]byte, error)
}

var goldenEncoders = []goldenEncoder{
	{"kitty", func(pngBytes []byte, _ *image.NRGBA) ([]byte, error) {
		return termgfx.AppendKitty(nil, pngBytes), nil
	}},
	{"iterm", func(pngBytes []byte, pixels *image.NRGBA) ([]byte, error) {
		size := pixels.Bounds().Size()
		return termgfx.AppendITerm(nil, pngBytes, size.X, size.Y)
	}},
	{"sixel", func(_ []byte, pixels *image.NRGBA) ([]byte, error) {
		size := pixels.Bounds().Size()
		return termgfx.AppendSixel(nil, pixels.Pix, size.X, size.Y)
	}},
}

func readGolden(t *testing.T, name string) []byte {
	t.Helper()
	data, err := os.ReadFile(filepath.Join(goldenDir, name))
	if err != nil {
		t.Fatal(err)
	}
	return data
}

func decodeGoldenPNG(t *testing.T, data []byte) *image.NRGBA {
	t.Helper()
	decoded, err := png.Decode(bytes.NewReader(data))
	if err != nil {
		t.Fatal(err)
	}
	pixels := image.NewNRGBA(decoded.Bounds())
	draw.Draw(pixels, pixels.Bounds(), decoded, decoded.Bounds().Min, draw.Src)
	return pixels
}

func firstDifference(got, want []byte) string {
	limit := min(len(got), len(want))
	offset := 0
	for offset < limit && got[offset] == want[offset] {
		offset++
	}
	from := max(offset-16, 0)
	return fmt.Sprintf("got %d bytes, want %d bytes, first difference at offset %d\n got ...%q\nwant ...%q",
		len(got), len(want), offset,
		got[from:min(offset+16, len(got))], want[from:min(offset+16, len(want))])
}

func TestEncoderGolden(t *testing.T) {
	for _, fixture := range goldenFixtures {
		t.Run(fixture, func(t *testing.T) {
			pngBytes := readGolden(t, fixture+".png")
			pixels := decodeGoldenPNG(t, pngBytes)
			for _, encoder := range goldenEncoders {
				t.Run(encoder.extension, func(t *testing.T) {
					got, err := encoder.encode(pngBytes, pixels)
					if err != nil {
						t.Fatal(err)
					}
					want := readGolden(t, fixture+"."+encoder.extension)
					if !bytes.Equal(got, want) {
						t.Fatal(firstDifference(got, want))
					}
				})
			}
		})
	}
}

func TestEncoderGoldenExercisesEveryByteRule(t *testing.T) {
	rules := []struct {
		extension string
		name      string
		marker    string
	}{
		{"kitty", "delete before transmit", "\x1b_Ga=d,d=A,q=2\x1b\\\x1b_Ga=T,f=100,i=1,q=2,m="},
		{"kitty", "continuation chunk", "\x1b_Gm=0;"},
		{"iterm", "inline file header", "\x1b]1337;File=inline=1;size="},
		{"iterm", "bell terminator", "\x07"},
		{"sixel", "raster attributes", "\x1bP7;0;0q\"1;1;"},
		{"sixel", "repeat introducer", "!"},
		{"sixel", "register separator", "$#"},
		{"sixel", "band separator", "-#"},
		{"sixel", "string terminator", "\x1b\\"},
	}
	for _, rule := range rules {
		t.Run(rule.extension+"/"+rule.name, func(t *testing.T) {
			for _, fixture := range goldenFixtures {
				if bytes.Contains(readGolden(t, fixture+"."+rule.extension), []byte(rule.marker)) {
					return
				}
			}
			t.Fatalf("no fixture golden contains %q", rule.marker)
		})
	}
}

func TestAppendSixelQuantisationBoundaries(t *testing.T) {
	boundaries := []struct{ value, level byte }{
		{0, 0}, {25, 0}, {26, 1}, {76, 1}, {77, 2}, {127, 2},
		{128, 3}, {178, 3}, {179, 4}, {229, 4}, {230, 5}, {255, 5},
	}
	for _, boundary := range boundaries {
		got, err := termgfx.AppendSixel(nil, []byte{boundary.value, 0, 0, 255}, 1, 1)
		if err != nil {
			t.Fatal(err)
		}
		want := fmt.Sprintf("#%d@\x1b\\", 36*int(boundary.level))
		if !bytes.HasSuffix(got, []byte(want)) {
			t.Errorf("red %d: tail %q, want register %d and %q", boundary.value, got[len(got)-12:], 36*int(boundary.level), want)
		}
	}
}
