package chart

import (
	"cmp"
	"math/bits"
	"slices"

	"github.com/gosuda/elegant-mermaid/internal/civil"
	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
)

type tickUnit uint8

const (
	tickSecond tickUnit = iota
	tickMinute
	tickHour
	tickDay
	tickWeek
	tickMonth
	tickYear
)

const (
	isoSunday    = 7
	isoThursday  = 4
	secondsMin   = 60
	secondsHour  = 3600
	daysPerWeek  = 7
	monthsInYear = 12
)

type tickRule struct {
	unit  tickUnit
	every int64
}

var autoTickTable = [...]struct {
	seconds int64
	rule    tickRule
}{
	{1, tickRule{tickSecond, 1}}, {5, tickRule{tickSecond, 5}}, {15, tickRule{tickSecond, 15}}, {30, tickRule{tickSecond, 30}},
	{60, tickRule{tickMinute, 1}}, {300, tickRule{tickMinute, 5}}, {900, tickRule{tickMinute, 15}}, {1800, tickRule{tickMinute, 30}},
	{3600, tickRule{tickHour, 1}}, {10800, tickRule{tickHour, 3}}, {21600, tickRule{tickHour, 6}}, {43200, tickRule{tickHour, 12}},
	{86400, tickRule{tickDay, 1}}, {172800, tickRule{tickDay, 2}}, {604800, tickRule{tickWeek, 1}},
	{2592000, tickRule{tickMonth, 1}}, {7776000, tickRule{tickMonth, 3}}, {31536000, tickRule{tickYear, 1}},
}

var explicitUnitMillis = map[string]int64{
	"second": 1000, "minute": 60_000, "hour": 3_600_000, "day": 86_400_000, "week": 604_800_000, "month": 2_628_000_000,
}

var explicitUnits = map[string]tickUnit{
	"second": tickSecond, "minute": tickMinute, "hour": tickHour, "day": tickDay, "week": tickWeek, "month": tickMonth,
}

func autoTickRule(span int64) tickRule {
	last := len(autoTickTable) - 1
	i := 0
	for i <= last && autoTickTable[i].seconds*tickCount <= span {
		i++
	}
	if i == 0 {
		return autoTickTable[0].rule
	}
	if i > last {
		return autoTickTable[last].rule
	}
	hi, lo := bits.Mul64(uint64(span), uint64(span))
	product := uint64(tickCount*tickCount) * uint64(autoTickTable[i-1].seconds) * uint64(autoTickTable[i].seconds)
	if hi == 0 && lo < product {
		return autoTickTable[i-1].rule
	}
	return autoTickTable[i].rule
}

func (p *ganttPlan) tickRuleFor() (rule tickRule, weekday int64) {
	g := p.g
	span := p.d1 - p.d0
	if span < 0 {
		span = -span
	}
	unit, ok := explicitUnits[g.TickUnit]
	if !ok || g.TickEvery <= 0 {
		return autoTickRule(span), isoSunday
	}
	if measure.CeilDiv(span*1000, g.TickEvery*explicitUnitMillis[g.TickUnit]) > p.c.estimateCap {
		return autoTickRule(span), isoSunday
	}
	weekday, found := civil.WeekdayIndex(g.Weekday)
	if !found {
		weekday = isoSunday
	}
	return tickRule{unit, g.TickEvery}, weekday
}

type tickSink struct {
	out    []int64
	lo, hi int64
	limit  int
	capped bool
}

func (s *tickSink) add(t int64) bool {
	switch {
	case t > s.hi:
		return false
	case t < s.lo:
		return true
	case len(s.out) == s.limit:
		s.capped = true
		return false
	}
	s.out = append(s.out, t)
	return true
}

func (s *tickSink) fields(blockSeconds, blockWidth, step, unitSeconds int64) {
	for start := geom.FloorDiv(s.lo, blockSeconds) * blockSeconds; ; start += blockSeconds {
		for j := int64(0); j < blockWidth; j += step {
			if !s.add(start + j*unitSeconds) {
				return
			}
		}
	}
}

func (s *tickSink) days(step int64) {
	f := civil.Split(s.lo)
	for y, m := f.Year, f.Month; ; {
		for d := int64(1); d <= civil.DaysInMonth(y, m); d += step {
			if !s.add(civil.DaysFromCivil(y, m, d) * civil.SecondsPerDay) {
				return
			}
		}
		y, m = nextMonth(y, m)
	}
}

func nextMonth(y, m int64) (int64, int64) {
	if m == monthsInYear {
		return y + 1, 1
	}
	return y, m + 1
}

func (s *tickSink) weeks(step, weekday int64) {
	shift := geom.FloorMod(isoThursday-weekday, daysPerWeek)
	days := measure.CeilDiv(s.lo, civil.SecondsPerDay)
	count := measure.CeilDiv(measure.CeilDiv(days+shift, daysPerWeek), step) * step
	for ; ; count += step {
		if !s.add((count*daysPerWeek - shift) * civil.SecondsPerDay) {
			return
		}
	}
}

func (s *tickSink) months(step int64) {
	for y := civil.Split(s.lo).Year; ; y++ {
		for m := int64(0); m < monthsInYear; m += step {
			if !s.add(civil.DaysFromCivil(y, m+1, 1) * civil.SecondsPerDay) {
				return
			}
		}
	}
}

func (s *tickSink) years() {
	for y := civil.Split(s.lo).Year; ; y++ {
		if !s.add(civil.DaysFromCivil(y, 1, 1) * civil.SecondsPerDay) {
			return
		}
	}
}

func (s *tickSink) run(rule tickRule, weekday int64) {
	switch rule.unit {
	case tickSecond:
		s.fields(secondsMin, secondsMin, rule.every, 1)
	case tickMinute:
		s.fields(secondsHour, secondsMin, rule.every, secondsMin)
	case tickHour:
		s.fields(civil.SecondsPerDay, 24, rule.every, secondsHour)
	case tickDay:
		s.days(rule.every)
	case tickWeek:
		s.weeks(rule.every, weekday)
	case tickMonth:
		s.months(rule.every)
	default:
		s.years()
	}
}

func (p *ganttPlan) computeTicks() {
	rule, weekday := p.tickRuleFor()
	sink := &tickSink{lo: min(p.d0, p.d1), hi: max(p.d0, p.d1), limit: int(p.c.tickCap)}
	sink.run(rule, weekday)
	p.capped = sink.capped
	p.ticks = sink.out
	if p.d1 < p.d0 {
		slices.Reverse(p.ticks)
	}
	format := cmp.Or(p.g.AxisForm, ganttDefaultFm)
	p.tickText = make([]string, len(p.ticks))
	for i, t := range p.ticks {
		text, unsupported := civil.Format(t, format)
		if unsupported != "" {
			text, _ = civil.Format(t, ganttDefaultFm)
		}
		p.tickText[i] = text
	}
}
