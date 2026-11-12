package class

import "regexp"

type directionRule struct {
	kind    string
	pattern *regexp.Regexp
}

var directionRules = []directionRule{
	{"direction_tb", regexp.MustCompile(`direction[ \t]+TB`)},
	{"direction_bt", regexp.MustCompile(`direction[ \t]+BT`)},
	{"direction_rl", regexp.MustCompile(`direction[ \t]+RL`)},
	{"direction_lr", regexp.MustCompile(`direction[ \t]+LR`)},
}

func (l *lexer) directionLine() bool {
	end := l.at
	for end < len(l.src) && l.src[end] != '\r' && l.src[end] != '\n' {
		end++
	}
	for _, rule := range directionRules {
		if !rule.pattern.Match(l.src[l.at:end]) {
			continue
		}
		start := l.at
		l.at = end
		l.emit(rule.kind, start, end)
		return true
	}
	return false
}
