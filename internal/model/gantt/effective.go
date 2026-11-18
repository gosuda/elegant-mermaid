package gantt

import "cmp"

func (m *Model) EffectiveAxisFormat() string {
	format := m.AxisFormat
	if format == "" && m.DateFormat == "D" {
		format = DayAxisForm
	}
	if config, ok := m.ConfigString("axisFormat"); format == "" && ok {
		format = config
	}
	format = cmp.Or(format, DefaultAxisForm)
	if unsupportedAxisCode(format) != "" {
		return DefaultAxisForm
	}
	return format
}

func (m *Model) TickRule() (every int64, unit string) {
	text := m.TickInterval
	if config, ok := m.ConfigString("tickInterval"); text == "" && ok {
		text = config
	}
	every, unit, ok := parseTickInterval(text)
	if !ok || unit == "millisecond" {
		return 0, ""
	}
	return every, unit
}
