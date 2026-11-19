package gantt

import "github.com/gosuda/elegant-mermaid/internal/civil"

const fallbackYearLimit = 10000

type scan struct {
	text string
	at   int
}

func (s *scan) digits(n int) (int64, bool) {
	if s.at+n > len(s.text) {
		return 0, false
	}
	var v int64
	for i := range n {
		c := s.text[s.at+i]
		if c < '0' || c > '9' {
			return 0, false
		}
		v = v*10 + int64(c-'0')
	}
	s.at += n
	return v, true
}

func (s *scan) accept(c byte) bool {
	if s.at < len(s.text) && s.text[s.at] == c {
		s.at++
		return true
	}
	return false
}

func (s *scan) done() bool { return s.at == len(s.text) }

type civilDate struct{ year, month, day int64 }

func (s *scan) year() (int64, bool) {
	if s.at < len(s.text) && (s.text[s.at] == '+' || s.text[s.at] == '-') {
		negative := s.text[s.at] == '-'
		s.at++
		v, ok := s.digits(6)
		if negative {
			return -v, ok && v != 0
		}
		return v, ok
	}
	return s.digits(4)
}

func (s *scan) group(sep byte, into *int64) bool {
	if !s.accept(sep) {
		return true
	}
	v, ok := s.digits(2)
	*into = v
	return ok
}

func (s *scan) isoDate() (civilDate, bool) {
	year, ok := s.year()
	if !ok {
		return civilDate{}, false
	}
	d := civilDate{year, 1, 1}
	if !s.group('-', &d.month) || !s.group('-', &d.day) {
		return civilDate{}, false
	}
	return d, true
}

func (s *scan) slashDate() (civilDate, bool) {
	year, ok := s.digits(4)
	if !ok || !s.accept('/') {
		return civilDate{}, false
	}
	month, ok := s.number(2)
	if !ok || !s.accept('/') {
		return civilDate{}, false
	}
	day, ok := s.number(2)
	return civilDate{year, month, day}, ok
}

func (s *scan) number(limit int) (int64, bool) {
	var v int64
	n := 0
	for n < limit && s.at < len(s.text) && s.text[s.at] >= '0' && s.text[s.at] <= '9' {
		v = v*10 + int64(s.text[s.at]-'0')
		s.at++
		n++
	}
	return v, n > 0
}

type clock struct{ hour, minute, second int64 }

func (s *scan) fraction() bool {
	if !s.accept('.') {
		return true
	}
	_, ok := s.number(1 << 20)
	return ok
}

func (s *scan) seconds(c *clock) bool {
	if !s.accept(':') {
		return true
	}
	var ok bool
	c.second, ok = s.digits(2)
	return ok && s.fraction()
}

func (s *scan) clock() (clock, bool) {
	var c clock
	var ok bool
	if c.hour, ok = s.digits(2); !ok || !s.accept(':') {
		return clock{}, false
	}
	if c.minute, ok = s.digits(2); !ok || !s.seconds(&c) {
		return clock{}, false
	}
	return c, true
}

func (s *scan) offset() bool {
	if s.accept('Z') {
		return true
	}
	if s.at >= len(s.text) || (s.text[s.at] != '+' && s.text[s.at] != '-') {
		return true
	}
	s.at++
	if _, ok := s.digits(2); !ok {
		return false
	}
	s.accept(':')
	if s.at < len(s.text) {
		_, ok := s.digits(2)
		return ok
	}
	return true
}

func validClock(c clock) bool {
	if c.hour == 24 {
		return c.minute == 0 && c.second == 0
	}
	return c.hour < 24 && c.minute < 60 && c.second < 60
}

func validDate(d civilDate) bool {
	return d.month >= 1 && d.month <= 12 && d.day >= 1 && d.day <= civil.DaysInMonth(d.year, d.month) &&
		d.year >= -fallbackYearLimit && d.year <= fallbackYearLimit
}

func fallbackSeconds(text string) (int64, bool) {
	s := &scan{text: text}
	date, ok := s.isoDate()
	if !ok {
		s.at = 0
		date, ok = s.slashDate()
	}
	if !ok {
		return 0, false
	}
	var c clock
	if s.accept('T') || s.accept(' ') {
		if c, ok = s.clock(); !ok || !s.offset() {
			return 0, false
		}
	}
	if !s.done() || !validDate(date) || !validClock(c) {
		return 0, false
	}
	return civil.Join(date.year, date.month, date.day, c.hour, c.minute, c.second), true
}
