package class

import "regexp"

type directionRule struct {
	kind    string
	pattern *regexp.Regexp
}

var directionRules = []directionRule{
	{"direction_tb", regexp.MustCompile(`^[^\r\n]*direction\s+TB[^\r\n]*`)},
	{"direction_bt", regexp.MustCompile(`^[^\r\n]*direction\s+BT[^\r\n]*`)},
	{"direction_rl", regexp.MustCompile(`^[^\r\n]*direction\s+RL[^\r\n]*`)},
	{"direction_lr", regexp.MustCompile(`^[^\r\n]*direction\s+LR[^\r\n]*`)},
}

func (l *lexer) directionLine() bool {
	for _, rule := range directionRules {
		length := len(rule.pattern.Find(l.src[l.at:]))
		if length == 0 {
			continue
		}
		start := l.at
		l.at += length
		l.emit(rule.kind, start, l.at)
		return true
	}
	return false
}
