package sankey

import "strings"

type ValueKind uint8

const (
	ValueFinite ValueKind = iota
	ValueNonFinite
	ValueOverflow
)

type Value struct {
	Kind        ValueKind
	Thousandths int64
}

const (
	maxThousandths = 1<<31 - 1
	maxExponent    = 999999999
	scaleDigits    = 3
	maxDigits      = 10
	infinityWord   = "Infinity"
)

type decimal struct {
	negative bool
	digits   string
	fraction int64
	exponent int64
}

func ParseValue(field string) Value {
	d, ok := scanDecimal(strings.TrimSpace(field))
	if !ok {
		return Value{Kind: ValueNonFinite}
	}
	return d.thousandths()
}

func isDigit(c byte) bool { return c >= '0' && c <= '9' }

func digitsEnd(s string, at int) int {
	for at < len(s) && isDigit(s[at]) {
		at++
	}
	return at
}

func scanDecimal(text string) (decimal, bool) {
	var d decimal
	at := 0
	if at < len(text) && (text[at] == '+' || text[at] == '-') {
		d.negative = text[at] == '-'
		at++
	}
	if strings.HasPrefix(text[at:], infinityWord) {
		return decimal{}, false
	}
	wholeEnd := digitsEnd(text, at)
	whole := text[at:wholeEnd]
	end, frac := wholeEnd, ""
	if end < len(text) && text[end] == '.' {
		fracEnd := digitsEnd(text, end+1)
		frac, end = text[end+1:fracEnd], fracEnd
	}
	if whole == "" && frac == "" {
		return decimal{}, false
	}
	d.digits = strings.TrimLeft(whole+frac, "0")
	d.fraction = int64(len(frac))
	d.exponent = scanExponent(text, end)
	return d, true
}

func scanExponent(text string, at int) int64 {
	if at >= len(text) || text[at] != 'e' && text[at] != 'E' {
		return 0
	}
	at++
	negative := at < len(text) && text[at] == '-'
	if at < len(text) && (text[at] == '+' || text[at] == '-') {
		at++
	}
	var value int64
	for _, c := range []byte(text[at:digitsEnd(text, at)]) {
		value = min(value*10+int64(c-'0'), maxExponent)
	}
	if negative {
		return -value
	}
	return value
}

func (d decimal) thousandths() Value {
	if d.digits == "" {
		return Value{Kind: ValueFinite}
	}
	size := int64(len(d.digits))
	p := d.exponent - d.fraction + scaleDigits
	if size+p > maxDigits {
		return Value{Kind: ValueOverflow}
	}
	t := d.scaled(size, p)
	if t > maxThousandths {
		return Value{Kind: ValueOverflow}
	}
	if d.negative {
		t = -t
	}
	return Value{Kind: ValueFinite, Thousandths: t}
}

func (d decimal) scaled(size, p int64) int64 {
	if p >= 0 {
		return leading(d.digits) * pow10(p)
	}
	if size < -p {
		return 0
	}
	keep := size + p
	t := leading(d.digits[:keep])
	if d.digits[keep] >= '5' {
		t++
	}
	return t
}

func leading(digits string) int64 {
	var v int64
	for _, c := range []byte(digits) {
		v = v*10 + int64(c-'0')
	}
	return v
}

func pow10(p int64) int64 {
	v := int64(1)
	for range p {
		v *= 10
	}
	return v
}
