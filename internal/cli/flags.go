package cli

import (
	"fmt"
	"strconv"
	"strings"
)

type flagToken struct {
	name, value string
	hasValue    bool
}

func isFlagArg(arg string) bool {
	return len(arg) > 1 && arg[0] == '-'
}

func splitFlag(arg string) (flagToken, bool) {
	body := strings.TrimPrefix(strings.TrimPrefix(arg, "-"), "-")
	if strings.HasPrefix(body, "-") {
		return flagToken{}, false
	}
	name, value, hasValue := strings.Cut(body, "=")
	return flagToken{name: name, value: value, hasValue: hasValue}, true
}

func (t flagToken) operand(arg string, rest []string) (string, []string, error) {
	if t.hasValue {
		return t.value, rest, nil
	}
	if len(rest) == 0 {
		return "", nil, fmt.Errorf("missing value for %s", arg)
	}
	return rest[0], rest[1:], nil
}

func (t flagToken) switchValue() (bool, error) {
	if !t.hasValue {
		return true, nil
	}
	on, err := strconv.ParseBool(t.value)
	if err != nil {
		return false, invalidValue(t.value, "--"+t.name, "true, false")
	}
	return on, nil
}

func unknownFlag(arg, command string) error {
	return fmt.Errorf("unknown flag %s; run emd %s --help", arg, command)
}
