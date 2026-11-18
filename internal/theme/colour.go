package theme

import "fmt"

type Colour struct {
	R, G, B uint8
}

var ErrBadColour = fmt.Errorf("theme: bad colour")

type HSL struct {
	H, S, L int32
}

type Delta struct {
	H, S, L int32
}

const (
	hueArc       = 360
	satMax       = 100
	lightMax     = 100
	channelMax   = 255
	sectorWidth  = 60
	percentScale = 100
)

func ParseHex(s string) (Colour, error) {
	if len(s) == 0 || s[0] != '#' {
		return Colour{}, fmt.Errorf("%w %q", ErrBadColour, s)
	}
	digits := s[1:]
	switch len(digits) {
	case 3:
		return parseShort(digits)
	case 6:
		return parseLong(digits)
	default:
		return Colour{}, fmt.Errorf("%w %q", ErrBadColour, s)
	}
}

func parseShort(digits string) (Colour, error) {
	var raw [3]uint8
	for i := range raw {
		d, ok := hexDigit(digits[i])
		if !ok {
			return Colour{}, fmt.Errorf("%w %q", ErrBadColour, "#"+digits)
		}
		raw[i] = d * 17
	}
	return Colour{R: raw[0], G: raw[1], B: raw[2]}, nil
}

func parseLong(digits string) (Colour, error) {
	var raw [3]uint8
	for i := range raw {
		hi, okHi := hexDigit(digits[2*i])
		lo, okLo := hexDigit(digits[2*i+1])
		if !okHi || !okLo {
			return Colour{}, fmt.Errorf("%w %q", ErrBadColour, "#"+digits)
		}
		raw[i] = hi<<4 | lo
	}
	return Colour{R: raw[0], G: raw[1], B: raw[2]}, nil
}

func hexDigit(b byte) (uint8, bool) {
	switch {
	case b >= '0' && b <= '9':
		return b - '0', true
	case b >= 'a' && b <= 'f':
		return b - 'a' + 10, true
	case b >= 'A' && b <= 'F':
		return b - 'A' + 10, true
	default:
		return 0, false
	}
}

func (c Colour) Hex() string {
	const digits = "0123456789abcdef"
	out := [7]byte{'#', 0, 0, 0, 0, 0, 0}
	for i, v := range [3]uint8{c.R, c.G, c.B} {
		out[1+2*i] = digits[v>>4]
		out[2+2*i] = digits[v&0x0F]
	}
	return string(out[:])
}

func (c Colour) HSL() HSL {
	r, g, b := int64(c.R), int64(c.G), int64(c.B)
	hi := max(r, g, b)
	lo := min(r, g, b)
	span := hi - lo
	light := floorDiv(percentScale*(hi+lo)+channelMax, 2*channelMax)
	if span == 0 {
		return HSL{H: 0, S: 0, L: int32(light)}
	}
	den := channelMax - absOf(hi+lo-channelMax)
	sat := floorDiv(2*percentScale*span+den, 2*den)
	return HSL{H: int32(hueOf(r, g, b, hi, span)), S: int32(sat), L: int32(light)}
}

func hueOf(r, g, b, hi, span int64) int64 {
	var phase int64
	switch hi {
	case r:
		phase = sectorWidth * (g - b)
	case g:
		phase = sectorWidth*(b-r) + 2*sectorWidth*span
	case b:
		phase = sectorWidth*(r-g) + 4*sectorWidth*span
	}
	return floorMod(floorDiv(2*phase+span, 2*span), hueArc)
}

func FromHSL(h HSL) Colour {
	hue := int64(h.H)
	sat := clampRange(int64(h.S), satMax)
	light := clampRange(int64(h.L), lightMax)
	c := floorDiv((lightMax-absOf(2*light-lightMax))*sat*channelMax+5000, 10000)
	x := floorDiv(c*(sectorWidth-absOf(floorMod(hue, 2*sectorWidth)-sectorWidth))+30, sectorWidth)
	offset := floorDiv(channelMax*light+50, percentScale) - floorDiv(c, 2)
	r, g, b := hueSectorChannels(floorMod(hue, hueArc)/sectorWidth, c, x)
	return Colour{
		R: clampChannel(r + offset),
		G: clampChannel(g + offset),
		B: clampChannel(b + offset),
	}
}

func hueSectorChannels(sector, c, x int64) (int64, int64, int64) {
	switch sector {
	case 0:
		return c, x, 0
	case 1:
		return x, c, 0
	case 2:
		return 0, c, x
	case 3:
		return 0, x, c
	case 4:
		return x, 0, c
	case 5:
		return c, 0, x
	default:
		panic("theme: invalid hue sector")
	}
}

func clampChannel(v int64) uint8 {
	return uint8(clampRange(v, channelMax))
}

func clampRange(v, hi int64) int64 {
	return min(max(v, 0), hi)
}

func Adjust(c Colour, d Delta) Colour {
	base := c.HSL()
	return FromHSL(HSL{
		H: int32(floorMod(int64(base.H)+int64(d.H), hueArc)),
		S: int32(clampRange(int64(base.S)+int64(d.S), satMax)),
		L: int32(clampRange(int64(base.L)+int64(d.L), lightMax)),
	})
}

func Darken(c Colour, amount int32) Colour {
	base := c.HSL()
	base.L = int32(clampRange(int64(base.L)-int64(amount), lightMax))
	return FromHSL(base)
}

func Lighten(c Colour, amount int32) Colour {
	return Adjust(c, Delta{L: amount})
}

func Invert(c Colour) Colour {
	return Colour{R: channelMax - c.R, G: channelMax - c.G, B: channelMax - c.B}
}

func MkBorderDark(c Colour) Colour {
	return Adjust(c, Delta{S: -40, L: 10})
}

func MkBorderLight(c Colour) Colour {
	return Adjust(c, Delta{S: -40, L: -10})
}

func absOf(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

func floorDiv(a, b int64) int64 {
	q := a / b
	if a%b != 0 && (a < 0) != (b < 0) {
		q--
	}
	return q
}

func floorMod(a, b int64) int64 {
	return a - floorDiv(a, b)*b
}
