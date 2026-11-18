package icon

const (
	fixedScale = 1_000_000
	fixedLimit = 1_000_000_000_000
)

type point struct{ x, y int64 }

type command struct {
	op byte
	p  [3]point
}

func isDigit(c byte) bool { return '0' <= c && c <= '9' }

func isSpace(c byte) bool { return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' }

func scanFraction(s string, i int) (int64, int) {
	var frac int64
	places := 0
	for i < len(s) && isDigit(s[i]) {
		switch {
		case places < 6:
			frac = frac*10 + int64(s[i]-'0')
		case places == 6 && s[i] >= '5':
			frac++
		}
		places++
		i++
	}
	for ; places < 6; places++ {
		frac *= 10
	}
	return frac, i
}

func scanSign(s string, i int) (bool, int) {
	if i < len(s) && (s[i] == '+' || s[i] == '-') {
		return s[i] == '-', i + 1
	}
	return false, i
}

func scanWhole(s string, i int) (int64, int, int, bool) {
	var whole int64
	digits := 0
	for i < len(s) && isDigit(s[i]) {
		whole = whole*10 + int64(s[i]-'0')
		if whole >= fixedScale {
			return 0, 0, i, false
		}
		digits++
		i++
	}
	return whole, digits, i, true
}

func scanFractionPart(s string, i int) (int64, int, int) {
	if i >= len(s) || s[i] != '.' {
		return 0, 0, i
	}
	frac, end := scanFraction(s, i+1)
	return frac, end - i - 1, end
}

func atExponent(s string, i int) bool {
	return i < len(s) && (s[i] == 'e' || s[i] == 'E')
}

func scanNumber(s string, i int) (int64, int, bool) {
	neg, i := scanSign(s, i)
	whole, digits, i, ok := scanWhole(s, i)
	if !ok {
		return 0, i, false
	}
	frac, fractionDigits, i := scanFractionPart(s, i)
	if digits+fractionDigits == 0 || atExponent(s, i) {
		return 0, i, false
	}
	v := whole*fixedScale + frac
	if neg {
		v = -v
	}
	return v, i, true
}

func parseDecimal(s string) (int64, bool) {
	v, end, ok := scanNumber(s, 0)
	return v, ok && end == len(s)
}

type pen struct {
	s       string
	i       int
	cur     point
	start   point
	reflect point
	prev    byte
	out     []command
}

func (p *pen) skipSeparators() {
	for p.i < len(p.s) && isSpace(p.s[p.i]) {
		p.i++
	}
	if p.i < len(p.s) && p.s[p.i] == ',' {
		p.i++
		for p.i < len(p.s) && isSpace(p.s[p.i]) {
			p.i++
		}
	}
}

func (p *pen) number() (int64, bool) {
	p.skipSeparators()
	v, end, ok := scanNumber(p.s, p.i)
	p.i = end
	return v, ok && v > -fixedLimit && v < fixedLimit
}

func (p *pen) numbers(n int) ([6]int64, bool) {
	var out [6]int64
	for k := range n {
		v, ok := p.number()
		if !ok {
			return out, false
		}
		out[k] = v
	}
	return out, true
}

func argCount(op byte) int {
	switch op {
	case 'M', 'L', 'T':
		return 2
	case 'H', 'V':
		return 1
	case 'C':
		return 6
	case 'S', 'Q':
		return 4
	}
	return -1
}

func upper(c byte) byte {
	if 'a' <= c && c <= 'z' {
		return c - 'a' + 'A'
	}
	return c
}

func isCommand(c byte) bool { return argCount(upper(c)) >= 0 || upper(c) == 'Z' }

func parsePath(d string) ([]command, bool) {
	p := &pen{s: d}
	var op byte
	for {
		p.skipSeparators()
		if p.i >= len(p.s) {
			return p.out, len(p.out) > 0
		}
		if isCommand(p.s[p.i]) {
			op = p.s[p.i]
			p.i++
		}
		if !p.allowed(op) || !p.apply(op) {
			return nil, false
		}
		op = followUp(op)
	}
}

func (p *pen) allowed(op byte) bool {
	if len(p.out) == 0 {
		return upper(op) == 'M'
	}
	return op != 0
}

func followUp(op byte) byte {
	switch op {
	case 'M':
		return 'L'
	case 'm':
		return 'l'
	case 'Z', 'z':
		return 0
	}
	return op
}

func (p *pen) apply(op byte) bool {
	u := upper(op)
	if u == 'Z' {
		p.close()
		return true
	}
	args, ok := p.numbers(argCount(u))
	if !ok {
		return false
	}
	if op != u {
		p.makeAbsolute(u, &args)
	}
	p.dispatch(u, args)
	return p.inRange()
}

func (p *pen) makeAbsolute(u byte, a *[6]int64) {
	switch u {
	case 'H':
		a[0] += p.cur.x
	case 'V':
		a[0] += p.cur.y
	default:
		for k := 0; k+1 < argCount(u); k += 2 {
			a[k] += p.cur.x
			a[k+1] += p.cur.y
		}
	}
}

func (p *pen) dispatch(u byte, a [6]int64) {
	switch u {
	case 'M', 'L':
		p.move(u, point{a[0], a[1]})
	case 'H':
		p.move('L', point{a[0], p.cur.y})
	case 'V':
		p.move('L', point{p.cur.x, a[0]})
	case 'C':
		p.cubic(point{a[0], a[1]}, point{a[2], a[3]}, point{a[4], a[5]})
	case 'S':
		p.cubic(p.smoothControl('C'), point{a[0], a[1]}, point{a[2], a[3]})
	case 'Q':
		p.quad(point{a[0], a[1]}, point{a[2], a[3]})
	case 'T':
		p.quad(p.smoothControl('Q'), point{a[0], a[1]})
	}
}

func (p *pen) smoothControl(kind byte) point {
	if p.prev != kind {
		return p.cur
	}
	return point{2*p.cur.x - p.reflect.x, 2*p.cur.y - p.reflect.y}
}

func (p *pen) move(op byte, to point) {
	p.out = append(p.out, command{op: op, p: [3]point{to}})
	p.cur = to
	if op == 'M' {
		p.start = to
	}
	p.prev = op
}

func (p *pen) cubic(c1, c2, to point) {
	p.out = append(p.out, command{op: 'C', p: [3]point{c1, c2, to}})
	p.cur, p.reflect, p.prev = to, c2, 'C'
}

func (p *pen) quad(c, to point) {
	p.out = append(p.out, command{op: 'Q', p: [3]point{c, to}})
	p.cur, p.reflect, p.prev = to, c, 'Q'
}

func (p *pen) close() {
	p.out = append(p.out, command{op: 'Z'})
	p.cur, p.prev = p.start, 'Z'
}

func (p *pen) inRange() bool {
	last := p.out[len(p.out)-1]
	for _, q := range last.p {
		if q.x <= -fixedLimit || q.x >= fixedLimit || q.y <= -fixedLimit || q.y >= fixedLimit {
			return false
		}
	}
	return true
}
