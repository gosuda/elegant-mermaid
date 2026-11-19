package termgfx_test

import (
	"bytes"
	"encoding/base64"
	"errors"
	"fmt"
	"image"
	"image/draw"
	"image/png"
	"strconv"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
)

func pngWireInput(t *testing.T) (*bytes.Buffer, *image.NRGBA) {
	t.Helper()
	img := image.NewNRGBA(image.Rect(0, 0, 64, 48))
	state := uint32(1)
	for i := range img.Pix {
		state ^= state << 13
		state ^= state >> 17
		state ^= state << 5
		img.Pix[i] = byte(state)
	}
	var input bytes.Buffer
	if err := png.Encode(&input, img); err != nil {
		t.Fatal(err)
	}
	return &input, img
}

func TestAppendKittyPNGWire(t *testing.T) {
	input, img := pngWireInput(t)
	wire, ok := strings.CutPrefix(string(termgfx.AppendKitty([]byte("prefix"), input.Bytes())), "prefix\x1b_Ga=d,d=A,q=2\x1b\\")
	if !ok {
		t.Fatal("Kitty must preserve destination and delete previous images first")
	}
	var payload strings.Builder
	chunks := 0
	for wire != "" {
		control, data, rest := parseKittyFrame(t, wire)
		more := "0"
		if rest != "" {
			more = "1"
		}
		want := "m=" + more
		if chunks == 0 {
			want = "a=T,f=100,i=1,q=2," + want
		}
		if control != want {
			t.Fatalf("Kitty chunk %d: control %q, size %d", chunks, control, len(data))
		}
		payload.WriteString(data)
		wire = rest
		chunks++
	}
	if chunks < 2 {
		t.Fatal("PNG must exercise Kitty continuation framing")
	}
	assertPNGPayload(t, payload.String(), input.Bytes(), img)
}

func parseKittyFrame(t *testing.T, wire string) (string, string, string) {
	t.Helper()
	body, rest, complete := strings.Cut(wire, "\x1b\\")
	body, apc := strings.CutPrefix(body, "\x1b_G")
	if !complete || !apc {
		t.Fatalf("unterminated Kitty APC: %q", body)
	}
	control, data, separated := strings.Cut(body, ";")
	if !separated || len(data) > 4096 || (rest != "" && len(data) != 4096) {
		t.Fatalf("Kitty APC control %q: missing separator or invalid payload size %d", control, len(data))
	}
	return control, data, rest
}

func TestAppendITermPNGWire(t *testing.T) {
	input, img := pngWireInput(t)
	iterm, err := termgfx.AppendITerm([]byte("prefix"), input.Bytes(), 64, 48)
	if err != nil {
		t.Fatal(err)
	}
	header := fmt.Sprintf("prefix\x1b]1337;File=inline=1;size=%d;width=64px;height=48px;preserveAspectRatio=0:", input.Len())
	encoded, prefix := strings.CutPrefix(string(iterm), header)
	encoded, suffix := strings.CutSuffix(encoded, "\x07")
	if !prefix || !suffix {
		t.Fatal("iTerm file metadata, destination prefix, or BEL framing is incorrect")
	}
	assertPNGPayload(t, encoded, input.Bytes(), img)
}

func assertPNGPayload(t *testing.T, encoded string, want []byte, img *image.NRGBA) {
	t.Helper()
	decoded, err := base64.StdEncoding.Strict().DecodeString(encoded)
	if err != nil || !bytes.Equal(decoded, want) {
		t.Fatalf("base64 did not preserve PNG bytes: %v", err)
	}
	got, err := png.Decode(bytes.NewReader(decoded))
	if err != nil {
		t.Fatal(err)
	}
	if got.Bounds() != img.Bounds() {
		t.Fatalf("decoded image bounds %v, want %v", got.Bounds(), img.Bounds())
	}
	pixels := image.NewNRGBA(got.Bounds())
	draw.Draw(pixels, pixels.Bounds(), got, got.Bounds().Min, draw.Src)
	if !bytes.Equal(pixels.Pix, img.Pix) {
		t.Fatal("decoded PNG pixel channels changed")
	}
}

func TestAppendSixelBufferBounds(t *testing.T) {
	for _, size := range [][2]int{{int(^uint(0) >> 1), 2}, {2, 2}} {
		got, err := termgfx.AppendSixel([]byte("keep"), []byte{0, 0, 0, 255}, size[0], size[1])
		if !errors.Is(err, termgfx.ErrBuffer) || string(got) != "keep" {
			t.Fatalf("size %v: got %q, %v; want unchanged destination and ErrBuffer", size, got, err)
		}
	}
}

func TestAppendSixelPixels(t *testing.T) {
	const width, height = 5, 7
	rowColors := [height][3]byte{
		{},
		{255, 0, 0},
		{0, 255, 0},
		{},
		{0, 0, 255},
		{},
		{255, 0, 0},
	}
	rgba := make([]byte, width*height*4)
	for i := range width * height {
		copy(rgba[4*i:4*i+3], rowColors[i/width][:])
		rgba[4*i+3] = byte(i)
	}
	out, err := termgfx.AppendSixel(nil, rgba, width, height)
	if err != nil {
		t.Fatal(err)
	}
	body, prefix := strings.CutPrefix(string(out), "\x1bP7;0;0q\"1;1;5;7")
	body, suffix := strings.CutSuffix(body, "\x1b\\")
	if !prefix || !suffix {
		t.Fatal("Sixel raster dimensions or DCS/ST framing incorrect")
	}
	body = assertSixelPalette(t, body)
	bands := strings.Split(body, "-")
	if len(bands) != 2 {
		t.Fatalf("seven pixel rows require two sixel bands, got %q", body)
	}
	planes := strings.Split(bands[0], "$")
	if len(planes) != 4 {
		t.Fatalf("first band needs four color planes separated by $, got %q", bands[0])
	}
	assertSixelPlane(t, planes[0], 0, (1<<0)|(1<<3)|(1<<5))
	assertSixelPlane(t, planes[1], 5, 1<<4)
	assertSixelPlane(t, planes[2], 30, 1<<2)
	assertSixelPlane(t, planes[3], 180, 1<<1)
	assertSixelPlane(t, bands[1], 180, 1)
}

func assertSixelPalette(t *testing.T, body string) string {
	t.Helper()
	for n := range 216 {
		entry := fmt.Sprintf("#%d;2;%d;%d;%d", n, 20*(n/36), 20*(n/6%6), 20*(n%6))
		var ok bool
		body, ok = strings.CutPrefix(body, entry)
		if !ok {
			t.Fatalf("incorrect six-level palette register %d", n)
		}
	}
	return body
}

func assertSixelPlane(t *testing.T, plane string, register int, mask byte) {
	t.Helper()
	data, ok := strings.CutPrefix(plane, "#"+strconv.Itoa(register))
	if !ok {
		t.Fatalf("plane %q does not select register %d", plane, register)
	}
	if len(data) < 3 || data[0] != '!' {
		t.Fatalf("five equal columns must use repeat encoding: %q", data)
	}
	count, err := strconv.Atoi(data[1 : len(data)-1])
	if err != nil || count != 5 {
		t.Fatalf("repeat count in %q: %d, %v; want five columns", data, count, err)
	}
	got := data[len(data)-1] - 63
	if got != mask {
		t.Fatalf("register %d row mask %06b, want %06b", register, got, mask)
	}
}
