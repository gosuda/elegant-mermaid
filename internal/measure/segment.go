package measure

import "unicode/utf8"

type Cluster struct {
	Text string
}

func Segment(s string) []Cluster {
	if s == "" {
		return nil
	}
	starts, scalars := scalarStarts(s)
	clusters := make([]Cluster, 0, len(scalars))
	state := stateAt(scalars[0])
	start := 0
	for i := 1; i < len(scalars); i++ {
		next := scalars[i]
		if state.breaksBefore(graphemeProp(next), incbProp(next)) {
			clusters = append(clusters, Cluster{Text: s[starts[start]:starts[i]]})
			start = i
		}
		state.advance(graphemeProp(next), incbProp(next))
	}
	return append(clusters, Cluster{Text: s[starts[start]:]})
}

func ClusterWidth(c Cluster) int32 {
	first := FirstScalar(c)
	prop := graphemeProp(first)
	if prop == propExtend || prop == propZWJ {
		return 0
	}
	if scalarWidth(first) == 2 {
		return 2
	}
	var pictographic bool
	for _, cp := range c.Text {
		prop := graphemeProp(cp)
		if cp == combiningKeycap {
			return 2
		}
		if cp == presentationSelector && pictographic {
			return 2
		}
		if prop == propExtendedPictographic {
			pictographic = true
		}
	}
	return 1
}

func CellWidth(s string) (int32, error) {
	var total int64
	for _, c := range Segment(s) {
		total += int64(ClusterWidth(c))
	}
	return checkedI32(total)
}

func FirstScalar(c Cluster) rune {
	cp, _ := utf8.DecodeRuneInString(c.Text)
	return cp
}

func LastScalar(c Cluster) rune {
	var last rune
	for _, cp := range c.Text {
		last = cp
	}
	return last
}

func scalarStarts(s string) ([]int, []rune) {
	starts := make([]int, 0, len(s)+1)
	scalars := make([]rune, 0, len(s))
	for offset, cp := range s {
		starts = append(starts, offset)
		scalars = append(scalars, cp)
	}
	return append(starts, len(s)), scalars
}

func isControl(prop uint8) bool {
	return prop == propCR || prop == propLF || prop == propControl
}

func hangulJoins(prev, next uint8) bool {
	switch prev {
	case propL:
		return next == propL || next == propV || next == propLV || next == propLVT
	case propLV, propV:
		return next == propV || next == propT
	case propLVT, propT:
		return next == propT
	default:
		return false
	}
}

func attachesToPrevious(next uint8) bool {
	return next == propExtend || next == propZWJ || next == propSpacingMark
}

func controlBreak(prev, next uint8) (bool, bool) {
	if prev == propCR && next == propLF {
		return true, false
	}
	if isControl(prev) || isControl(next) {
		return true, true
	}
	return false, false
}

type breakState struct {
	prev        uint8
	pictRun     bool
	gb11Pending bool
	linkerRun   bool
	riRun       int
}

func stateAt(cp rune) breakState {
	state := breakState{}
	state.advance(graphemeProp(cp), incbProp(cp))
	return state
}

func (st *breakState) advance(prop, incb uint8) {
	pending := st.pictRun
	st.advanceLinker(incb)
	st.pictRun = nextPictRun(prop, st.pictRun)
	st.gb11Pending = prop == propZWJ && pending
	st.advanceRegional(prop)
	st.prev = prop
}

func (st *breakState) advanceLinker(incb uint8) {
	switch incb {
	case incbLinker:
		st.linkerRun = true
	case incbExtend:
	default:
		st.linkerRun = false
	}
}

func (st *breakState) advanceRegional(prop uint8) {
	if prop == propRegionalIndicator {
		st.riRun++
		return
	}
	st.riRun = 0
}

func nextPictRun(prop uint8, pictRun bool) bool {
	if prop == propExtendedPictographic {
		return true
	}
	return prop == propExtend && pictRun
}

func (st *breakState) breaksBefore(next, nextIncb uint8) bool {
	if decided, doBreak := controlBreak(st.prev, next); decided {
		return doBreak
	}
	if hangulJoins(st.prev, next) || attachesToPrevious(next) {
		return false
	}
	if st.prev == propPrepend {
		return false
	}
	if st.linkerRun && nextIncb == incbConsonant {
		return false
	}
	if st.gb11Pending && next == propExtendedPictographic {
		return false
	}
	return st.regionalJoins(next)
}

func (st *breakState) regionalJoins(next uint8) bool {
	if st.prev != propRegionalIndicator || next != propRegionalIndicator {
		return true
	}
	return st.riRun%2 == 0
}
