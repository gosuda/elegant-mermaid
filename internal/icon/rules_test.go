package icon

import (
	"fmt"
	"math"
	"math/big"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func ratFloor(r *big.Rat) int64 {
	return new(big.Int).Div(r.Num(), r.Denom()).Int64()
}

func ratRound(r *big.Rat) int64 {
	return ratFloor(new(big.Rat).Add(r, big.NewRat(1, 2)))
}

func magnitude(whole, fraction string) *big.Rat {
	digits, ok := new(big.Int).SetString(whole+fraction, 10)
	if !ok {
		digits = new(big.Int)
	}
	return new(big.Rat).SetFrac(digits, new(big.Int).Exp(big.NewInt(10), big.NewInt(int64(len(fraction))), nil))
}

func oracleMicro(sign, whole, fraction string) (int64, bool) {
	micro := ratRound(new(big.Rat).Mul(magnitude(whole, fraction), big.NewRat(1_000_000, 1)))
	if sign == "-" {
		micro = -micro
	}
	return micro, micro > -1_000_000_000_000 && micro < 1_000_000_000_000
}

func sourceValue(t *testing.T, text string) *big.Rat {
	t.Helper()
	sign := ""
	if strings.HasPrefix(text, "-") {
		sign, text = "-", text[1:]
	}
	whole, fraction, _ := strings.Cut(text, ".")
	micro, ok := oracleMicro(sign, whole, fraction)
	if !ok {
		t.Fatalf("%q is out of range", text)
	}
	return big.NewRat(micro, 1_000_000)
}

type stream uint32

func (s *stream) next() uint32 {
	x := uint32(*s)
	x ^= x << 13
	x ^= x >> 17
	x ^= x << 5
	*s = stream(x)
	return x
}

func (s *stream) digits(n int) string {
	const alphabet = "0123456789999900005555"
	var b strings.Builder
	for range n {
		b.WriteByte(alphabet[s.next()%uint32(len(alphabet))])
	}
	return b.String()
}

func generatedNumber(s *stream) (text, sign, whole, fraction string) {
	sign = []string{"", "-", "+"}[s.next()%3]
	whole = s.digits(int(s.next() % 9))
	fraction = s.digits(int(s.next() % 13))
	if whole == "" && fraction == "" {
		fraction = s.digits(1)
	}
	text = sign + whole
	if fraction != "" || s.next()%2 == 0 {
		text += "." + fraction
	}
	return text, sign, whole, fraction
}

func TestPackPathNumbers(t *testing.T) {
	for i := range 2000 {
		state := stream(i + 1)
		text, sign, whole, fraction := generatedNumber(&state)
		want, inRange := oracleMicro(sign, whole, fraction)
		commands, ok := parsePath("M" + text + " 0")
		if ok != inRange {
			t.Fatalf("%q: supported=%v, rule says %v (value %d)", text, ok, inRange, want)
		}
		if ok && commands[0].p[0].x != want {
			t.Fatalf("%q: got %d, rule says %d", text, commands[0].p[0].x, want)
		}
	}
}

func TestPackPathNumbersRejectExponents(t *testing.T) {
	for _, text := range []string{"1e3", "1E3", "1e-3", "2.5e+1", ".5e1"} {
		if _, ok := parsePath("M" + text + " 0"); ok {
			t.Errorf("%q: exponent accepted", text)
		}
	}
}

func TestPackCoordinatesStayBelowTheLimit(t *testing.T) {
	for _, c := range []struct {
		data string
		ok   bool
	}{
		{"M999999.999999 0", true},
		{"M999999.9999995 0", false},
		{"M1000000 0", false},
		{"M999999 0h1", false},
		{"M999999 0h0.999999", true},
		{"M0 0C999999 0 1000000 0 0 0", false},
		{"M500000 0S0 0 0 0", true},
		{"M0 0C0 0 100000 0 900000 0S0 0 0 0", false},
		{"M-999999 0h-1", false},
	} {
		if _, ok := parsePath(c.data); ok != c.ok {
			t.Errorf("%q: supported=%v, rule says %v", c.data, ok, c.ok)
		}
	}
}

type iconCase struct {
	width, height, left, top string
	x0, y0, x1, y1           string
}

func parseRat(t *testing.T, text string) *big.Rat {
	t.Helper()
	r, ok := new(big.Rat).SetString(text)
	if !ok {
		t.Fatalf("bad rational %q", text)
	}
	return r
}

func unitRule(scale int64, v *big.Rat) int64 {
	return ratRound(new(big.Rat).Mul(v, big.NewRat(scale, 1)))
}

func iconPack(c iconCase) string {
	body := fmt.Sprintf(`<path d=\"M%s %sL%s %sz\"/>`, c.x0, c.y0, c.x1, c.y1)
	return fmt.Sprintf(`{"prefix":"p","icons":{"a":{"body":"%s","width":%s,"height":%s,"left":%s,"top":%s}}}`, body, c.width, c.height, c.left, c.top)
}

func expectedCorners(t *testing.T, c iconCase, at geom.Point) (string, bool) {
	t.Helper()
	w, h := parseRat(t, c.width), parseRat(t, c.height)
	side := w
	if h.Cmp(w) > 0 {
		side = h
	}
	if side.Cmp(big.NewRat(1, 1)) < 0 {
		return "", false
	}
	scale := max(1, ratRound(new(big.Rat).Quo(big.NewRat(1536, 1), side)))
	origin := func(at int32, size *big.Rat) int64 {
		return int64(at) + ratFloor(big.NewRat(1536-unitRule(scale, size), 2))
	}
	ox, oy := origin(at.X, w), origin(at.Y, h)
	left, top := parseRat(t, c.left), parseRat(t, c.top)
	point := func(x, y string) string {
		px := ox + unitRule(scale, new(big.Rat).Sub(sourceValue(t, x), left))
		py := oy + unitRule(scale, new(big.Rat).Sub(sourceValue(t, y), top))
		return fmt.Sprintf("%d,%d", px, py)
	}
	return fmt.Sprintf("M%s L%s Z", point(c.x0, c.y0), point(c.x1, c.y1)), true
}

func TestPackScaleAndOrigin(t *testing.T) {
	at := geom.Point{X: 100, Y: -50}
	for _, c := range []iconCase{
		{"24", "24", "0", "0", "0", "0", "24", "24"},
		{"20", "20", "0", "0", "0", "0", "20", "20"},
		{"28", "28", "0", "0", "3", "5", "25.5", "27"},
		{"32", "16", "0", "0", "0", "0", "32", "16"},
		{"16", "32", "0", "0", "1.5", "2.25", "9", "30.125"},
		{"17.5", "17.5", "0", "0", "0.000001", "0.0000005", "17.5", "17.499999"},
		{"1792", "1792", "0", "0", "100", "200", "1700", "1790"},
		{"1536", "1536", "0", "0", "100", "200", "1500", "1500"},
		{"1024", "1024", "0", "0", "100", "200", "1000", "1000"},
		{"8", "4", "2", "2", "2", "2", "10", "6"},
		{"24", "24", "-3", "4.5", "-3", "4.5", "21", "28.5"},
		{"1", "1", "0", "0", "0", "0", "1", "1"},
		{"999999", "999999", "0", "0", "0", "0", "999999", "1"},
		{"0.999999", "0.5", "0", "0", "0", "0", "1", "1"},
		{"0.5", "0.5", "0", "0", "0", "0", "0.5", "0.5"},
	} {
		want, supported := expectedCorners(t, c, at)
		got := Draw([]*Pack{mustPack(t, iconPack(c))}, "p:a", at, scene.ProfileVector)
		if got.Missing == supported {
			t.Fatalf("%+v: missing=%v, rule says supported=%v", c, got.Missing, supported)
		}
		if !supported {
			continue
		}
		path, ok := got.Items[0].(*scene.Path)
		if !ok || commandsText(path.Commands) != want {
			t.Errorf("%+v: got %v, rule says %s", c, got.Items, want)
		}
	}
}

func TestPackResultOutsideInt32IsUnsupported(t *testing.T) {
	pack := mustPack(t, `{"prefix":"p","icons":{"a":{"body":"<path d=\"M0 0h20v20z\"/>","width":20,"height":20}}}`)
	for _, c := range []struct {
		at      geom.Point
		missing bool
	}{
		{geom.Point{X: math.MaxInt32 - 1538}, false},
		{geom.Point{X: math.MaxInt32 - 1537}, true},
		{geom.Point{X: math.MinInt32 + 2}, false},
		{geom.Point{X: math.MinInt32 + 1}, true},
		{geom.Point{Y: math.MaxInt32 - 1538}, false},
		{geom.Point{Y: math.MaxInt32 - 1537}, true},
		{geom.Point{Y: math.MinInt32 + 2}, false},
		{geom.Point{Y: math.MinInt32 + 1}, true},
	} {
		if got := Draw([]*Pack{pack}, "p:a", c.at, scene.ProfileVector); got.Missing != c.missing {
			t.Errorf("%v: missing=%v, rule says %v", c.at, got.Missing, c.missing)
		}
	}
}

func drawn(t *testing.T, data string) string {
	t.Helper()
	pack := mustPack(t, fmt.Sprintf(`{"prefix":"p","width":24,"height":24,"icons":{"a":{"body":"<path d=\"%s\"/>"}}}`, data))
	got := Draw([]*Pack{pack}, "p:a", geom.Point{}, scene.ProfileVector)
	if got.Missing {
		return "missing"
	}
	return commandsText(got.Items[0].(*scene.Path).Commands)
}

func TestPackQuadraticToCubic(t *testing.T) {
	scale := int64(64)
	unit := func(v int64) int64 { return v * scale }
	third := func(a, c int64) int64 { return ratRound(big.NewRat(a+2*c, 3)) }
	type pt struct{ x, y int64 }
	from, control, to := pt{unit(2), unit(3)}, pt{unit(10), unit(20)}, pt{unit(7), unit(1)}
	want := fmt.Sprintf("M%d,%d C%d,%d,%d,%d,%d,%d", from.x, from.y,
		third(from.x, control.x), third(from.y, control.y), third(to.x, control.x), third(to.y, control.y), to.x, to.y)
	if got := drawn(t, "M2 3Q10 20 7 1"); got != want {
		t.Errorf("quadratic: got %s, rule says %s", got, want)
	}
}

func TestPackRelativeAndSmoothCommandsFollowSVG(t *testing.T) {
	for _, c := range []struct{ relative, absolute string }{
		{"m1 1l2 3h4v5z", "M1 1L3 4L7 4L7 9Z"},
		{"M1 1 2 3 4 5", "M1 1L2 3L4 5"},
		{"m1 1 2 3 4 5", "m1 1l2 3l4 5"},
		{"m1 1c1 2 3 4 5 6s7 8 9 10", "M1 1C2 3 4 5 6 7C8 9 13 15 15 17"},
		{"M0 0C1 2 3 4 5 6S9 10 11 12", "M0 0C1 2 3 4 5 6C7 8 9 10 11 12"},
		{"M0 0S9 10 11 12", "M0 0C0 0 9 10 11 12"},
		{"M0 0Q3 3 5 1T9 1", "M0 0Q3 3 5 1Q7 -1 9 1"},
		{"M0 0T9 1", "M0 0Q0 0 9 1"},
		{"M0 0Q3 3 5 1S9 10 11 12", "M0 0Q3 3 5 1C5 1 9 10 11 12"},
		{"M0 0C1 2 3 4 5 6T9 1", "M0 0C1 2 3 4 5 6Q5 6 9 1"},
		{"M2 2L6 6zm3 3l1 1", "M2 2L6 6ZM5 5L6 6"},
		{"M2 2 6 6z l1 1", "M2 2L6 6ZL3 3"},
		{"m1 1q2 2 4 0t4 0", "M1 1Q3 3 5 1Q7 -1 9 1"},
	} {
		if r, a := drawn(t, c.relative), drawn(t, c.absolute); r != a || r == "missing" {
			t.Errorf("%q: %s; %q: %s", c.relative, r, c.absolute, a)
		}
	}
}

func bodyDraw(t *testing.T, body string) (items int, missing bool) {
	t.Helper()
	data := fmt.Sprintf(`{"prefix":"p","width":24,"height":24,"icons":{"a":{"body":%q}}}`, body)
	got := Draw([]*Pack{mustPack(t, data)}, "p:a", geom.Point{}, scene.ProfileVector)
	return len(got.Items), got.Missing
}

func TestPackBodies(t *testing.T) {
	const path = `<path d="M0 0h8v8z"/>`
	for _, c := range []struct {
		name, body string
		paths      int
		missing    bool
	}{
		{"blank", "", 0, false},
		{"white space only", " \t\r\n\f", 0, false},
		{"one path", path, 1, false},
		{"two paths", path + path, 2, false},
		{"ASCII space between", path + " \t\r\n\f" + path, 2, false},
		{"explicit close", `<path d="M0 0h8v8z"></path>`, 1, false},
		{"fill currentColor", `<path fill="currentColor" d='M0 0h8v8z'/>`, 1, false},
		{"adjacent attributes", `<path d="M0 0h8v8z"fill="currentColor"/>`, 1, false},
		{"last d wins", `<path d="bad" d="M0 0h8v8z"/>`, 1, false},
		{"no-break space between", path + "\u00a0" + path, 0, true},
		{"leading no-break space", "\u00a0" + path, 0, true},
		{"text after", path + "text", 0, true},
		{"other element", `<circle cx="1" cy="1" r="1"/>`, 0, true},
		{"group", "<g>" + path + "</g>", 0, true},
		{"other attribute", `<path fill-rule="evenodd" d="M0 0h8v8z"/>`, 0, true},
		{"fill colour", `<path fill="red" d="M0 0h8v8z"/>`, 0, true},
		{"stroke", `<path stroke="red" d="M0 0h8v8z"/>`, 0, true},
		{"no d", `<path fill="currentColor"/>`, 0, true},
		{"empty d", `<path d=""/>`, 0, true},
		{"space in close", `<path d="M0 0h8v8z"> </path>`, 0, true},
		{"space before equals", `<path d ="M0 0h8v8z"/>`, 0, true},
		{"space after equals", `<path d= "M0 0h8v8z"/>`, 0, true},
		{"no space after name", `<pathd="M0 0h8v8z"/>`, 0, true},
		{"unquoted", `<path d=M0/>`, 0, true},
		{"unclosed", `<path d="M0 0h8v8z"`, 0, true},
		{"open without close", `<path d="M0 0h8v8z">`, 0, true},
		{"comment", "<!-- c -->" + path, 0, true},
		{"arc", `<path d="M0 0A1 1 0 0 1 2 2"/>`, 0, true},
		{"starts with L", `<path d="L1 1"/>`, 0, true},
		{"double comma", `<path d="M0,,0h8v8z"/>`, 0, true},
		{"comma then command", `<path d="M0 0,h8v8z"/>`, 1, false},
		{"comma before first number", `<path d="M,0 0h8v8z"/>`, 1, false},
		{"number after close", `<path d="M0 0z 1 1"/>`, 0, true},
		{"one of two bad", path + `<path d="M0 0A1 1"/>`, 0, true},
	} {
		items, missing := bodyDraw(t, c.body)
		wantItems := c.paths
		if c.missing {
			wantItems = 1
		}
		if missing != c.missing || items != wantItems {
			t.Errorf("%s: items=%d missing=%v, rule says items=%d missing=%v", c.name, items, missing, wantItems, c.missing)
		}
	}
}

const (
	unsupportedPack = `{"prefix":"p","icons":{"a":{"body":"<circle cx=\"1\" cy=\"1\" r=\"1\"/>"}}}`
	supportedPack   = `{"prefix":"p","icons":{"a":{"body":"<path d=\"M0 0h16v16z\"/>"}}}`
)

func TestPackFirstDefiningPackWinsEvenWhenUnsupported(t *testing.T) {
	bad, good := mustPack(t, unsupportedPack), mustPack(t, supportedPack)
	for _, c := range []struct {
		packs   []*Pack
		missing bool
	}{
		{[]*Pack{bad, good}, true},
		{[]*Pack{good, bad}, false},
		{[]*Pack{bad}, true},
		{[]*Pack{good}, false},
	} {
		if got := Draw(c.packs, "p:a", geom.Point{}, scene.ProfileVector); got.Missing != c.missing {
			t.Errorf("missing=%v, rule says %v", got.Missing, c.missing)
		}
	}
}

func TestMissingIconDrawsTheInkUnknownSymbolInCells(t *testing.T) {
	for _, packs := range [][]*Pack{nil, {mustPack(t, unsupportedPack)}} {
		got := Draw(packs, "p:a", geom.Point{X: 5, Y: 6}, scene.ProfileCell)
		symbol, ok := got.Items[0].(*scene.SymbolRef)
		if !got.Missing || len(got.Items) != 1 || !ok || symbol.Symbol != "unknown" || symbol.Style != "ink" || symbol.At != (geom.Point{X: 5, Y: 6}) {
			t.Errorf("%d packs: %+v", len(packs), got)
		}
	}
}
