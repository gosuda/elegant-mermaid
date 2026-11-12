package gen

import (
	"errors"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

const layeredCaseZero = `flowchart TD
n0[birch0]
n1[fjord1]
n2[pine2]
n3[birch3]
n1 --> n2
`

var (
	nodeDecl   = regexp.MustCompile(`^n(\d+)\[`)
	edgeDecl   = regexp.MustCompile(`^n(\d+) --> n(\d+)$`)
	messageRE  = regexp.MustCompile(`^n(\d+)(->>|-->>|->|-->)n(\d+): [a-z]+\d+$`)
	gridNode   = regexp.MustCompile(`^n(\d+)\["[a-z]+\d+"\]:[12]$`)
	treeLine   = regexp.MustCompile(`^( *)([a-z]+)(\d+)$`)
	participa  = regexp.MustCompile(`^participant n(\d+)$`)
	colonCmd   = regexp.MustCompile(`^(branch|checkout|merge) ([a-z]+\d+|main)$`)
	nonterm    = regexp.MustCompile(`nonterminal\('r(\d+)'\)`)
	ruleLine   = regexp.MustCompile(`^r(\d+) = .+ ;$`)
	columnsRE  = regexp.MustCompile(`^columns [1-4]$`)
	headers    = map[string]string{"layered": "flowchart TD", "sequence": "sequenceDiagram", "grid": "block-beta", "tree": "mindmap", "lanes": "gitGraph", "chart": "xychart-beta", "railroad": "railroad-beta"}
	containers = []string{"sequence(", "choice("}
	wrappers   = []string{"optional(", "oneOrMore(", "zeroOrMore("}
	leaves     = []string{"terminal('", "nonterminal('", "special('"}
)

func TestStreamChain(t *testing.T) {
	want := []uint32{270369, 67634689, 2647435461, 307599695, 2398689233}
	r := newStream(0)
	for i, w := range want {
		if got := r.next(); got != w {
			t.Fatalf("draw %d: got %d want %d", i+1, got, w)
		}
	}
}

func TestLayeredCaseZero(t *testing.T) {
	got, err := Source("layered", 0)
	if err != nil {
		t.Fatalf("Source: %v", err)
	}
	if got != layeredCaseZero {
		t.Fatalf("case 0:\n%q\nwant:\n%q", got, layeredCaseZero)
	}
}

func TestFamilies(t *testing.T) {
	want := []string{"layered", "sequence", "grid", "tree", "lanes", "chart", "railroad"}
	got := Families()
	if strings.Join(got, ",") != strings.Join(want, ",") {
		t.Fatalf("families: %v", got)
	}
	got[0] = "mutated"
	if Families()[0] != "layered" {
		t.Fatal("Families returned shared state")
	}
}

func TestSourceErrors(t *testing.T) {
	if _, err := Source("nope", 0); !errors.Is(err, ErrFamily) {
		t.Fatalf("unknown family: %v", err)
	}
	if _, err := Source("layered", -1); !errors.Is(err, ErrCase) {
		t.Fatalf("negative case: %v", err)
	}
	if _, err := Source("layered", caseCount); !errors.Is(err, ErrCase) {
		t.Fatalf("case past end: %v", err)
	}
}

func TestDeterministic(t *testing.T) {
	for _, family := range Families() {
		first, err := Source(family, 42)
		if err != nil {
			t.Fatalf("%s: %v", family, err)
		}
		second, err := Source(family, 42)
		if err != nil {
			t.Fatalf("%s: %v", family, err)
		}
		if first != second {
			t.Fatalf("%s: unstable output", family)
		}
	}
}

func TestStructural(t *testing.T) {
	checks := map[string]func(t *testing.T, lines []string){
		"layered":  checkLayered,
		"sequence": checkSequence,
		"grid":     checkGrid,
		"tree":     checkTree,
		"lanes":    checkLanes,
		"chart":    checkChart,
		"railroad": checkRailroad,
	}
	for _, family := range Families() {
		t.Run(family, func(t *testing.T) {
			for i := range caseCount {
				text, err := Source(family, i)
				if err != nil {
					t.Fatalf("case %d: %v", i, err)
				}
				checks[family](t, checkFormat(t, i, text, headers[family]))
			}
		})
	}
}

func checkFormat(t *testing.T, i int, text, header string) []string {
	t.Helper()
	checkEncoding(t, i, text)
	lines := splitLines(t, i, text)
	if lines[0] != header {
		t.Fatalf("case %d: header %q", i, lines[0])
	}
	for _, line := range lines {
		checkLineShape(t, i, line)
	}
	return lines
}

func checkEncoding(t *testing.T, i int, text string) {
	t.Helper()
	if !isASCII(text) {
		t.Fatalf("case %d: not ASCII", i)
	}
	if !strings.HasSuffix(text, "\n") || strings.HasSuffix(text, "\n\n") {
		t.Fatalf("case %d: bad final newline", i)
	}
	if strings.ContainsAny(text, "\r\t") {
		t.Fatalf("case %d: carriage return or tab", i)
	}
}

func splitLines(t *testing.T, i int, text string) []string {
	t.Helper()
	lines := strings.Split(strings.TrimSuffix(text, "\n"), "\n")
	if len(lines) < 2 {
		t.Fatalf("case %d: only %d lines", i, len(lines))
	}
	return lines
}

func checkLineShape(t *testing.T, i int, line string) {
	t.Helper()
	if line == "" {
		t.Fatalf("case %d: blank line", i)
	}
	if line != strings.TrimRight(line, " ") {
		t.Fatalf("case %d: trailing space in %q", i, line)
	}
}

func isASCII(text string) bool {
	for _, r := range text {
		if r > 0x7F {
			return false
		}
	}
	return true
}

func checkLayered(t *testing.T, lines []string) {
	t.Helper()
	nodes := 0
	edges := 0
	for _, line := range lines[1:] {
		if nodeDecl.MatchString(line) {
			nodes++
			continue
		}
		checkLayeredEdge(t, line, nodes)
		edges++
	}
	if nodes < 2 || nodes > 30 || edges < 1 || edges > nodes || len(lines) != nodes+edges+1 {
		t.Fatalf("layered: %d nodes, %d edges, %d lines", nodes, edges, len(lines))
	}
}

func checkLayeredEdge(t *testing.T, line string, nodes int) {
	t.Helper()
	m := edgeDecl.FindStringSubmatch(line)
	if m == nil {
		t.Fatalf("layered: bad line %q", line)
	}
	from, _ := strconv.Atoi(m[1])
	to, _ := strconv.Atoi(m[2])
	if from >= to {
		t.Fatalf("layered: edge %d -> %d not ascending", from, to)
	}
	if to >= nodes {
		t.Fatalf("layered: edge target %d outside %d nodes", to, nodes)
	}
}

func checkSequence(t *testing.T, lines []string) {
	t.Helper()
	actors := 0
	messages := 0
	for _, line := range lines[1:] {
		if m := participa.FindStringSubmatch(line); m != nil {
			index, _ := strconv.Atoi(m[1])
			if index != actors {
				t.Fatalf("sequence: participant %d at %d", index, actors)
			}
			actors++
			continue
		}
		checkSequenceMessage(t, line, actors)
		messages++
	}
	if actors < 2 || actors > 8 || messages < 1 || messages > 20 {
		t.Fatalf("sequence: %d actors, %d messages", actors, messages)
	}
}

func checkSequenceMessage(t *testing.T, line string, actors int) {
	t.Helper()
	m := messageRE.FindStringSubmatch(line)
	if m == nil {
		t.Fatalf("sequence: bad line %q", line)
	}
	from, _ := strconv.Atoi(m[1])
	to, _ := strconv.Atoi(m[3])
	if to == from {
		t.Fatalf("sequence: self message on %d", from)
	}
	if from >= actors || to >= actors {
		t.Fatalf("sequence: message %d -> %d outside %d actors", from, to, actors)
	}
}

func checkGrid(t *testing.T, lines []string) {
	t.Helper()
	if !columnsRE.MatchString(lines[1]) {
		t.Fatalf("grid: %q", lines[1])
	}
	nodes := 0
	edges := 0
	for _, line := range lines[2:] {
		if gridNode.MatchString(line) {
			nodes++
			continue
		}
		checkGridEdge(t, line, nodes)
		edges++
	}
	if nodes < 2 || nodes > 30 || edges > nodes-1 {
		t.Fatalf("grid: %d nodes, %d edges", nodes, edges)
	}
}

func checkGridEdge(t *testing.T, line string, nodes int) {
	t.Helper()
	m := edgeDecl.FindStringSubmatch(line)
	if m == nil {
		t.Fatalf("grid: bad line %q", line)
	}
	if to, _ := strconv.Atoi(m[2]); to >= nodes {
		t.Fatalf("grid: edge target %d outside %d nodes", to, nodes)
	}
}

func checkTree(t *testing.T, lines []string) {
	t.Helper()
	if len(lines) < 3 || len(lines) > 31 {
		t.Fatalf("tree: %d nodes", len(lines)-1)
	}
	seen := make([]bool, len(lines)-1)
	depth := -1
	for i, line := range lines[1:] {
		level, index := treeNode(t, line)
		if level > depth+1 || (i == 0) != (level == 0) {
			t.Fatalf("tree: depth %d after %d", level, depth)
		}
		if index >= len(seen) || seen[index] {
			t.Fatalf("tree: node %d repeated", index)
		}
		seen[index] = true
		depth = level
	}
	for index, ok := range seen {
		if !ok {
			t.Fatalf("tree: node %d missing", index)
		}
	}
}

func treeNode(t *testing.T, line string) (int, int) {
	t.Helper()
	m := treeLine.FindStringSubmatch(line)
	if m == nil {
		t.Fatalf("tree: bad line %q", line)
	}
	if len(m[1])%2 != 0 || len(m[1]) < 2 {
		t.Fatalf("tree: odd indent %q", line)
	}
	index, _ := strconv.Atoi(m[3])
	return (len(m[1]) - 2) / 2, index
}

func checkLanes(t *testing.T, lines []string) {
	t.Helper()
	if len(lines) < 4 || len(lines) > 31 {
		t.Fatalf("lanes: %d actions", len(lines)-1)
	}
	audit := laneAudit{current: "main", branches: 1}
	for _, line := range lines[1:] {
		audit.apply(t, line)
	}
	if audit.commits == 0 {
		t.Fatal("lanes: no commits")
	}
}

type laneAudit struct {
	current  string
	branches int
	commits  int
}

func (a *laneAudit) apply(t *testing.T, line string) {
	t.Helper()
	if line == "commit" {
		a.commits++
		return
	}
	m := colonCmd.FindStringSubmatch(line)
	if m == nil {
		t.Fatalf("lanes: bad line %q", line)
	}
	switch m[1] {
	case "branch":
		a.branches++
		if a.branches > 4 {
			t.Fatalf("lanes: %d branches", a.branches)
		}
		a.current = m[2]
	case "checkout":
		a.current = m[2]
	default:
		a.merge(t, m[2])
	}
}

func (a *laneAudit) merge(t *testing.T, name string) {
	t.Helper()
	if name == a.current {
		t.Fatalf("lanes: merge %q into itself", name)
	}
	a.commits++
}

func checkChart(t *testing.T, lines []string) {
	t.Helper()
	categories := listCount(t, lines[1], "x-axis [")
	if categories < 2 || categories > 12 {
		t.Fatalf("chart: %d categories", categories)
	}
	if lines[2] != "y-axis 0 --> 100" {
		t.Fatalf("chart: %q", lines[2])
	}
	for _, prefix := range []string{"bar [", "line ["} {
		checkChartValues(t, lineWith(lines, prefix), prefix, categories)
	}
}

func checkChartValues(t *testing.T, line, prefix string, categories int) {
	t.Helper()
	if got := listCount(t, line, prefix); got != categories {
		t.Fatalf("chart: %s holds %d of %d", prefix, got, categories)
	}
	inner, _ := strings.CutSuffix(strings.TrimPrefix(line, prefix), "]")
	for value := range strings.SplitSeq(inner, ", ") {
		if n, err := strconv.Atoi(value); err != nil || n < 0 || n > 100 {
			t.Fatalf("chart: value %q", value)
		}
	}
}

func lineWith(lines []string, prefix string) string {
	for _, line := range lines {
		if strings.HasPrefix(line, prefix) {
			return line
		}
	}
	return ""
}

func listCount(t *testing.T, line, open string) int {
	t.Helper()
	inner, ok := strings.CutPrefix(line, open)
	if !ok {
		t.Fatalf("chart: list line %q", line)
	}
	inner, ok = strings.CutSuffix(inner, "]")
	if !ok {
		t.Fatalf("chart: list line %q", line)
	}
	if inner == "" {
		return 0
	}
	return len(strings.Split(inner, ", "))
}

func checkRailroad(t *testing.T, lines []string) {
	t.Helper()
	rules := len(lines) - 1
	if rules < 1 || rules > 3 {
		t.Fatalf("railroad: %d rules", rules)
	}
	nodes := 0
	for _, line := range lines[1:] {
		nodes += checkRule(t, line, rules) + 1
	}
	if nodes > 12 {
		t.Fatalf("railroad: %d nodes", nodes)
	}
}

func checkRule(t *testing.T, line string, rules int) int {
	t.Helper()
	m := ruleLine.FindStringSubmatch(line)
	if m == nil {
		t.Fatalf("railroad: bad rule line %q", line)
	}
	body := strings.TrimSuffix(strings.TrimPrefix(line, "r"+m[1]+" = "), " ;")
	for _, ref := range nonterm.FindAllStringSubmatch(body, -1) {
		index, _ := strconv.Atoi(ref[1])
		if index >= rules {
			t.Fatalf("railroad: reference r%d of %d rules", index, rules)
		}
	}
	return leafCount(t, body)
}

func leafCount(t *testing.T, body string) int {
	t.Helper()
	if _, ok := cutPrefixes(body, leaves); ok {
		if _, closed := strings.CutSuffix(body, "')"); !closed {
			t.Fatalf("railroad: bad leaf %q", body)
		}
		return 0
	}
	if inner, ok := cutPrefixes(body, containers); ok {
		return containerCount(t, inner, body)
	}
	if inner, ok := cutPrefixes(body, wrappers); ok {
		if _, closed := strings.CutSuffix(inner, ")"); !closed {
			t.Fatalf("railroad: bad wrapper %q", body)
		}
		return 1
	}
	t.Fatalf("railroad: bad body %q", body)
	return 0
}

func cutPrefixes(body string, prefixes []string) (string, bool) {
	for _, prefix := range prefixes {
		if inner, ok := strings.CutPrefix(body, prefix); ok {
			return inner, true
		}
	}
	return body, false
}

func containerCount(t *testing.T, inner, body string) int {
	t.Helper()
	inner, closed := strings.CutSuffix(inner, ")")
	if !closed {
		t.Fatalf("railroad: bad container %q", body)
	}
	parts := len(strings.Split(inner, ", "))
	if parts < 2 || parts > 3 {
		t.Fatalf("railroad: %d children in %q", parts, body)
	}
	return parts
}
