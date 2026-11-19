package gen

import (
	"errors"
	"strconv"
	"strings"
)

const caseCount = 2000

var (
	ErrFamily = errors.New("unknown family")
	ErrCase   = errors.New("case index out of range")
)

var words = [16]string{
	"amber", "birch", "cedar", "delta", "ember", "fjord", "garnet", "harbor",
	"iris", "juniper", "kelp", "lumen", "maple", "nectar", "onyx", "pine",
}

var familyCases = []struct {
	name string
	emit func(*stream) []string
}{
	{"layered", layeredCase},
	{"sequence", sequenceCase},
	{"grid", gridCase},
	{"tree", treeCase},
	{"lanes", lanesCase},
	{"chart", chartCase},
	{"railroad", railroadCase},
}

type stream struct {
	s uint32
}

func newStream(i int) *stream {
	return &stream{s: uint32(i) + 1}
}

func (r *stream) next() uint32 {
	r.s ^= r.s << 13
	r.s ^= r.s >> 17
	r.s ^= r.s << 5
	return r.s
}

func (r *stream) draw(lo, hi int) int {
	return lo + int(r.next()%uint32(hi-lo+1))
}

func (r *stream) label(k int) string {
	return words[r.draw(0, 15)] + strconv.Itoa(k)
}

func Families() []string {
	out := make([]string, len(familyCases))
	for i, f := range familyCases {
		out[i] = f.name
	}
	return out
}

func Source(family string, i int) (string, error) {
	if i < 0 || i >= caseCount {
		return "", ErrCase
	}
	for _, f := range familyCases {
		if f.name == family {
			return strings.Join(f.emit(newStream(i)), "\n") + "\n", nil
		}
	}
	return "", ErrFamily
}

func layeredCase(r *stream) []string {
	n := r.draw(2, 30)
	lines := make([]string, 0, n+2)
	lines = append(lines, "flowchart TD")
	for i := range n {
		lines = append(lines, "n"+strconv.Itoa(i)+"["+r.label(i)+"]")
	}
	e := r.draw(1, n)
	for range e {
		a := r.draw(0, n-2)
		b := r.draw(a+1, n-1)
		lines = append(lines, "n"+strconv.Itoa(a)+" --> n"+strconv.Itoa(b))
	}
	return lines
}

func sequenceCase(r *stream) []string {
	actors := r.draw(2, 8)
	messages := r.draw(1, 20)
	arrows := [4]string{"->>", "-->>", "->", "-->"}
	lines := make([]string, 0, actors+messages+1)
	lines = append(lines, "sequenceDiagram")
	for i := range actors {
		lines = append(lines, "participant n"+strconv.Itoa(i))
	}
	for k := range messages {
		from := r.draw(0, actors-1)
		distance := r.draw(1, actors-1)
		to := (from + distance) % actors
		arrow := arrows[r.draw(0, 3)]
		lines = append(lines, "n"+strconv.Itoa(from)+arrow+"n"+strconv.Itoa(to)+": "+r.label(k))
	}
	return lines
}

func gridCase(r *stream) []string {
	columns := r.draw(1, 4)
	n := r.draw(2, 30)
	lines := make([]string, 0, n+2)
	lines = append(lines, "block-beta", "columns "+strconv.Itoa(columns))
	for i := range n {
		text := r.label(i)
		span := r.draw(1, 2)
		lines = append(lines, `n`+strconv.Itoa(i)+`["`+text+`"]:`+strconv.Itoa(span))
	}
	e := r.draw(0, n-1)
	for range e {
		a := r.draw(0, n-1)
		d := r.draw(1, n-1)
		b := (a + d) % n
		lines = append(lines, "n"+strconv.Itoa(a)+" --> n"+strconv.Itoa(b))
	}
	return lines
}

func treeCase(r *stream) []string {
	n := r.draw(2, 30)
	labels := make([]string, n)
	for i := range n {
		labels[i] = r.label(i)
	}
	parent := make([]int, n)
	for i := 1; i < n; i++ {
		parent[i] = r.draw(0, i-1)
	}
	lines := make([]string, 0, n+1)
	lines = append(lines, "mindmap")
	walkTree(n, parent, func(node, depth int) {
		lines = append(lines, strings.Repeat(" ", 2+2*depth)+labels[node])
	})
	return lines
}

func walkTree(n int, parent []int, visit func(node, depth int)) {
	var walk func(node, depth int)
	walk = func(node, depth int) {
		visit(node, depth)
		for c := 1; c < n; c++ {
			if parent[c] == node {
				walk(c, depth+1)
			}
		}
	}
	walk(0, 0)
}

type laneBranch struct {
	name      string
	head      int
	headOwner int
}

type laneState struct {
	branches []laneBranch
	current  int
	commits  int
	lines    []string
}

func lanesCase(r *stream) []string {
	st := &laneState{
		branches: []laneBranch{{name: "main", head: -1, headOwner: -1}},
		lines:    []string{"gitGraph"},
	}
	total := r.draw(3, 30)
	for range total {
		st.apply(r, r.draw(0, 9))
	}
	return st.lines
}

func (st *laneState) apply(r *stream, action int) {
	switch {
	case action <= 4:
		st.commit()
	case action == 5:
		st.maybeBranch(r)
	case action == 6:
		st.maybeCheckout(r)
	default:
		st.maybeMerge(r)
	}
}

func (st *laneState) advance() {
	st.commits++
	cur := &st.branches[st.current]
	cur.head = st.commits
	cur.headOwner = st.current
}

func (st *laneState) commit() {
	st.advance()
	st.lines = append(st.lines, "commit")
}

func (st *laneState) headSet() bool {
	return st.branches[st.current].head >= 0
}

func (st *laneState) maybeBranch(r *stream) {
	if len(st.branches) >= 4 || !st.headSet() {
		st.commit()
		return
	}
	name := words[r.draw(0, 15)] + strconv.Itoa(len(st.branches))
	st.branches = append(st.branches, laneBranch{
		name:      name,
		head:      st.branches[st.current].head,
		headOwner: st.branches[st.current].headOwner,
	})
	st.current = len(st.branches) - 1
	st.lines = append(st.lines, "branch "+name)
}

func (st *laneState) otherIndices() []int {
	others := make([]int, 0, len(st.branches)-1)
	for i := range st.branches {
		if i != st.current {
			others = append(others, i)
		}
	}
	return others
}

func (st *laneState) maybeCheckout(r *stream) {
	others := st.otherIndices()
	if len(others) == 0 {
		st.commit()
		return
	}
	st.current = others[r.draw(0, len(others)-1)]
	st.lines = append(st.lines, "checkout "+st.branches[st.current].name)
}

func (st *laneState) eligible() []int {
	if !st.headSet() {
		return nil
	}
	cur := st.branches[st.current]
	eligible := make([]int, 0, len(st.branches)-1)
	for i, b := range st.branches {
		if i == st.current || b.head < 0 || b.head == cur.head || cur.headOwner == i {
			continue
		}
		eligible = append(eligible, i)
	}
	return eligible
}

func (st *laneState) maybeMerge(r *stream) {
	eligible := st.eligible()
	if len(eligible) == 0 {
		st.commit()
		return
	}
	target := eligible[r.draw(0, len(eligible)-1)]
	st.lines = append(st.lines, "merge "+st.branches[target].name)
	st.advance()
}

func chartCase(r *stream) []string {
	n := r.draw(2, 12)
	labels := make([]string, n)
	for i := range n {
		labels[i] = r.label(i)
	}
	bars := r.drawValues(n)
	lines := r.drawValues(n)
	return []string{
		"xychart-beta",
		"x-axis [" + strings.Join(labels, ", ") + "]",
		"y-axis 0 --> 100",
		"bar [" + strings.Join(bars, ", ") + "]",
		"line [" + strings.Join(lines, ", ") + "]",
	}
}

func (r *stream) drawValues(n int) []string {
	out := make([]string, n)
	for i := range n {
		out[i] = strconv.Itoa(r.draw(0, 100))
	}
	return out
}

type railroadForm struct {
	name     string
	children int
}

var railroadForms = [8]railroadForm{
	{name: "leaf"},
	{name: "leaf"},
	{name: "leaf"},
	{name: "sequence", children: -1},
	{name: "choice", children: -1},
	{name: "optional", children: 1},
	{name: "oneOrMore", children: 1},
	{name: "zeroOrMore", children: 1},
}

func railroadCase(r *stream) []string {
	rules := r.draw(1, 3)
	lines := make([]string, 0, rules+1)
	lines = append(lines, "railroad-beta")
	for i := range rules {
		lines = append(lines, "r"+strconv.Itoa(i)+" = "+railroadBody(r, rules, r.draw(0, 7))+" ;")
	}
	return lines
}

func railroadBody(r *stream, rules, kind int) string {
	form := railroadForms[kind]
	if form.children == 0 {
		return railroadLeaf(r, rules, kind)
	}
	count := form.children
	if count < 0 {
		count = r.draw(2, 3)
	}
	children := make([]string, count)
	for i := range count {
		children[i] = railroadLeaf(r, rules, r.draw(0, 2))
	}
	return form.name + "(" + strings.Join(children, ", ") + ")"
}

func railroadLeaf(r *stream, rules, kind int) string {
	switch kind {
	case 0:
		return "terminal('" + words[r.draw(0, 15)] + "')"
	case 1:
		return "nonterminal('r" + strconv.Itoa(r.draw(0, rules-1)) + "')"
	default:
		return "special('" + words[r.draw(0, 15)] + "')"
	}
}
