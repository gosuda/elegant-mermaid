package main

import (
	"cmp"
	"fmt"
	"regexp"
	"slices"
	"strings"
)

type layoutConstTable struct {
	*table
	consts []layoutConstInput
}

var leanConstNamePattern = regexp.MustCompile(`^[a-z][a-z0-9_]*(\.[a-z][a-z0-9_]*)*$`)

const leanLayoutConstNote = "-- `layoutconst` is opaque: a proof cannot evaluate a name lookup. A proof reads the\n" +
	"-- `LayoutConst` definitions below, one per key with each `.` written as `_`\n" +
	"-- (`class.padding` is `LayoutConst.class_padding`; `Pair.get` selects the profile).\n\n"

func (l *layoutConstTable) renderLean() ([]byte, error) {
	body, err := l.leanBody()
	if err != nil {
		return nil, err
	}
	defs, err := leanLayoutConstDefs(l.consts)
	if err != nil {
		return nil, err
	}
	return []byte(leanHeader + "import Elegant.Model\n\n" + leanLayoutConstNote + body + "\n" + defs), nil
}

func leanLayoutConstDefs(consts []layoutConstInput) (string, error) {
	sorted := slices.Clone(consts)
	slices.SortStableFunc(sorted, func(a, b layoutConstInput) int { return cmp.Compare(a.Name, b.Name) })
	var b strings.Builder
	b.WriteString("namespace LayoutConst\n\n")
	b.WriteString("structure Pair where\n  vector : Int\n  cell : Int\n\n")
	b.WriteString("def Pair.get (p : Pair) : Elegant.Profile → Int\n  | .vector => p.vector\n  | .cell => p.cell\n\n")
	owner := make(map[string]string, len(sorted))
	for _, c := range sorted {
		id, err := leanConstIdent(c.Name)
		if err != nil {
			return "", err
		}
		if prev, dup := owner[id]; dup {
			return "", fmt.Errorf("layout constants %q and %q share the Lean name %s", prev, c.Name, id)
		}
		owner[id] = c.Name
		fmt.Fprintf(&b, "def %s : Pair := ⟨%d, %d⟩\n", id, c.Vector, c.Cell)
	}
	b.WriteString("\nend LayoutConst\n")
	return b.String(), nil
}

func leanConstIdent(name string) (string, error) {
	if !leanConstNamePattern.MatchString(name) {
		return "", fmt.Errorf("layout constant %q is not dotted lower snake case", name)
	}
	return leanFieldName(strings.ReplaceAll(name, ".", "_")), nil
}
