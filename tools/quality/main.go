package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"math/big"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
	"strings"
	"sync"
)

type options struct {
	emd, kinds string
	jobs       int
	write      bool
}
type metric struct {
	Schema    int   `json:"schema"`
	HardOK    bool  `json:"hard_ok"`
	Nodes     int64 `json:"nodes"`
	Mean      int64 `json:"mean_node_extent"`
	Crossings int64 `json:"crossings"`
	Bends     int64 `json:"bends"`
	Against   int64 `json:"against_flow_edges"`
	Length    int64 `json:"total_route_length"`
	Area      int64 `json:"canvas_area"`
	Cost      int64 `json:"soft_cost"`
}
type score struct {
	Crossings int64 `json:"crossings"`
	Cost      int64 `json:"soft_cost"`
}
type fixture struct {
	Path             string
	Ours, Dagre, ELK metric
}
type exception struct {
	Path     string `json:"path"`
	Best     string `json:"best"`
	BestCost int64  `json:"best_soft_cost"`
	Ours     score  `json:"ours"`
	Dagre    score  `json:"dagre"`
	ELK      score  `json:"elk"`
}
type report struct {
	Schema     int         `json:"schema"`
	Fixtures   int         `json:"fixtures"`
	Exceptions []exception `json:"exceptions"`
}

func main() { os.Exit(execute(os.Args[1:], os.Stdout, os.Stderr)) }

func execute(args []string, out, errOut io.Writer) int {
	o, err := parseFlags(args, errOut)
	if errors.Is(err, flag.ErrHelp) {
		return 0
	}
	if err != nil {
		_, _ = fmt.Fprintln(errOut, err)
		return 2
	}
	passed, err := run(o, out, errOut)
	if err != nil {
		_, _ = fmt.Fprintln(errOut, err)
		return 2
	}
	if !passed {
		return 1
	}
	return 0
}

func parseFlags(args []string, out io.Writer) (options, error) {
	var o options
	f := flag.NewFlagSet("quality", flag.ContinueOnError)
	f.SetOutput(out)
	f.StringVar(&o.emd, "emd", "bin/emd-go", "metric scoring executable")
	f.StringVar(&o.kinds, "kinds", "flowchart", "comma-separated layered kinds")
	f.IntVar(&o.jobs, "jobs", runtime.NumCPU(), "maximum concurrent fixtures")
	f.BoolVar(&o.write, "write", false, "rewrite committed fixture and exception files (parent only)")
	if err := f.Parse(args); err != nil {
		return o, err
	}
	if f.NArg() != 0 || o.jobs < 1 || o.emd == "" {
		return o, errors.New("expected flags only, nonempty -emd, and -jobs >= 1")
	}
	_, err := selectedKinds(o.kinds)
	return o, err
}

func selectedKinds(text string) ([]string, error) {
	allowed := []string{"flowchart", "class", "state", "er", "requirement", "usecase", "c4", "agentflow", "swimlane"}
	kinds := strings.Split(text, ",")
	for _, kind := range kinds {
		if !slices.Contains(allowed, kind) {
			return nil, fmt.Errorf("invalid layered kind %q", kind)
		}
	}
	return kinds, nil
}

func fixturePaths(kinds string) ([]string, error) {
	selected, err := selectedKinds(kinds)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile("corpus/verdicts.json")
	if err != nil {
		return nil, err
	}
	var verdicts map[string]struct {
		Accept bool   `json:"accept"`
		Kind   string `json:"kind"`
	}
	if err := json.Unmarshal(data, &verdicts); err != nil {
		return nil, fmt.Errorf("corpus/verdicts.json: %w", err)
	}
	paths := make([]string, 0)
	for path, verdict := range verdicts {
		if verdict.Accept && slices.Contains(selected, verdict.Kind) {
			paths = append(paths, path)
		}
	}
	slices.Sort(paths)
	return paths, nil
}

func pathBytes(paths []string) []byte {
	if len(paths) == 0 {
		return []byte{}
	}
	return []byte(strings.Join(paths, "\n") + "\n")
}

func compareFile(path string, expected []byte, write bool) (bool, error) {
	if write {
		return true, os.WriteFile(path, expected, 0o644)
	}
	actual, err := os.ReadFile(path)
	if err != nil {
		return false, err
	}
	return bytes.Equal(actual, expected), nil
}

func prepareFixtures(o options, out, errOut io.Writer) ([]string, bool, error) {
	paths, err := fixturePaths(o.kinds)
	if err != nil {
		return nil, false, err
	}
	list := pathBytes(paths)
	if _, err := out.Write(list); err != nil {
		return nil, false, err
	}
	listOK, err := compareFile("corpus/quality-corpus.txt", list, o.write)
	if err != nil {
		return nil, false, err
	}
	if !listOK {
		_, _ = fmt.Fprintln(errOut, "corpus/quality-corpus.txt differs from computed fixture set")
	}
	return paths, listOK, nil
}

func run(o options, out, errOut io.Writer) (bool, error) {
	paths, listOK, err := prepareFixtures(o, out, errOut)
	if err != nil {
		return false, err
	}
	fixtures, err := collect(o, paths)
	if err != nil {
		return false, err
	}
	expected, err := exceptionBytes(fixtures)
	if err != nil {
		return false, err
	}
	exceptionsOK, err := compareFile("corpus/quality-exceptions.json", expected, o.write)
	if err != nil {
		return false, err
	}
	if !exceptionsOK {
		_, _ = fmt.Fprintln(errOut, "corpus/quality-exceptions.json differs from computed exceptions")
	}
	gates := evaluate(fixtures)
	if err := printReport(out, fixtures, gates); err != nil {
		return false, err
	}
	return listOK && exceptionsOK && !slices.Contains(gates[:], false), nil
}

func collect(o options, paths []string) ([]fixture, error) {
	fixtures := make([]fixture, len(paths))
	errs := make([]error, len(paths))
	jobs := make(chan int)
	var workers sync.WaitGroup
	for range min(o.jobs, len(paths)) {
		workers.Go(func() {
			for index := range jobs {
				fixtures[index], errs[index] = readFixture(o.emd, paths[index])
			}
		})
	}
	for index := range paths {
		jobs <- index
	}
	close(jobs)
	workers.Wait()
	for _, err := range errs {
		if err != nil {
			return nil, err
		}
	}
	return fixtures, nil
}

func readFixture(emd, path string) (fixture, error) {
	f := fixture{Path: path}
	targets := []*metric{&f.Ours, &f.Dagre, &f.ELK}
	engines := []string{"", "dagre", "elk"}
	for index, engine := range engines {
		args, err := metricArgs(path, engine)
		if err != nil {
			return f, err
		}
		m, err := readMetric(emd, args)
		if err != nil {
			return f, fmt.Errorf("%s (%s): %w", path, engine, err)
		}
		*targets[index] = m
	}
	return f, nil
}

func metricArgs(path, engine string) ([]string, error) {
	if engine == "" {
		return []string{"layout", "--metrics", path}, nil
	}
	dump := filepath.Join("corpus/.cache/quality", path+"."+engine+".json")
	if _, err := os.Stat(dump); err != nil {
		return nil, fmt.Errorf("baseline %s: %w", dump, err)
	}
	return []string{"layout", "--metrics", "--dump", dump}, nil
}

func readMetric(emd string, args []string) (metric, error) {
	cmd := exec.Command(emd, args...)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	data, err := cmd.Output()
	if err != nil {
		return metric{}, fmt.Errorf("%s %s: %w: %s", emd, strings.Join(args, " "), err, strings.TrimSpace(stderr.String()))
	}
	return decodeMetric(data)
}

func decodeMetric(data []byte) (metric, error) {
	var m metric
	var fields map[string]json.RawMessage
	if err := json.Unmarshal(data, &fields); err != nil {
		return m, err
	}
	keys := []string{"schema", "hard_ok", "nodes", "mean_node_extent", "crossings", "bends", "against_flow_edges", "total_route_length", "canvas_area", "soft_cost"}
	for _, key := range keys {
		value, ok := fields[key]
		if !ok || bytes.Equal(value, []byte("null")) {
			return m, fmt.Errorf("missing metric %s", key)
		}
	}
	if err := json.Unmarshal(data, &m); err != nil {
		return m, err
	}
	if m.Schema != 1 {
		return m, fmt.Errorf("unsupported metric schema %d", m.Schema)
	}
	values := []int64{m.Nodes, m.Mean, m.Crossings, m.Bends, m.Against, m.Length, m.Area, m.Cost}
	if slices.Min(values) < 0 || m.Mean < 1 {
		return m, errors.New("invalid negative metric or zero mean_node_extent")
	}
	return m, nil
}

func scaledCompare(a, scaleA, b, scaleB int64) int {
	var left, right big.Int
	left.Mul(big.NewInt(a), big.NewInt(scaleA))
	right.Mul(big.NewInt(b), big.NewInt(scaleB))
	return left.Cmp(&right)
}

func bestBaseline(f fixture) (string, metric) {
	if f.ELK.Cost < f.Dagre.Cost {
		return "elk", f.ELK
	}
	return "dagre", f.Dagre
}

func isException(f fixture) bool {
	_, best := bestBaseline(f)
	return scaledCompare(f.Ours.Cost, 100, best.Cost, 120) > 0
}

func exceptionBytes(fixtures []fixture) ([]byte, error) {
	r := report{Schema: 1, Fixtures: len(fixtures), Exceptions: make([]exception, 0)}
	for _, f := range fixtures {
		if !isException(f) {
			continue
		}
		name, best := bestBaseline(f)
		r.Exceptions = append(r.Exceptions, exception{f.Path, name, best.Cost, score{f.Ours.Crossings, f.Ours.Cost}, score{f.Dagre.Crossings, f.Dagre.Cost}, score{f.ELK.Crossings, f.ELK.Cost}})
	}
	slices.SortFunc(r.Exceptions, func(a, b exception) int { return strings.Compare(a.Path, b.Path) })
	var out bytes.Buffer
	encoder := json.NewEncoder(&out)
	encoder.SetEscapeHTML(false)
	if err := encoder.Encode(r); err != nil {
		return nil, err
	}
	return out.Bytes(), nil
}

func evaluate(fixtures []fixture) [4]bool {
	gates := [4]bool{true, true, true, true}
	var crossings, costs [3]big.Int
	exceptions := int64(0)
	for _, f := range fixtures {
		gates[0] = gates[0] && f.Ours.HardOK
		for index, m := range []metric{f.Ours, f.Dagre, f.ELK} {
			crossings[index].Add(&crossings[index], big.NewInt(m.Crossings))
			costs[index].Add(&costs[index], big.NewInt(m.Cost))
		}
		if isException(f) {
			exceptions++
		}
	}
	gates[1] = crossings[0].Cmp(&crossings[1]) <= 0 && crossings[0].Cmp(&crossings[2]) <= 0
	gates[2] = costs[0].Cmp(&costs[1]) <= 0 && costs[0].Cmp(&costs[2]) <= 0
	gates[3] = scaledCompare(exceptions, 20, int64(len(fixtures)), 1) <= 0
	return gates
}

func printReport(out io.Writer, fixtures []fixture, gates [4]bool) error {
	for _, f := range fixtures {
		_, err := fmt.Fprintf(out, "%s ours=%d/%d dagre=%d/%d elk=%d/%d exception=%t\n", f.Path, f.Ours.Crossings, f.Ours.Cost, f.Dagre.Crossings, f.Dagre.Cost, f.ELK.Crossings, f.ELK.Cost, isException(f))
		if err != nil {
			return err
		}
	}
	names := []string{"hard constraints", "total crossings", "total soft cost", "exceptions <= 5 percent"}
	for index, passed := range gates {
		verdict := "FAIL"
		if passed {
			verdict = "PASS"
		}
		if _, err := fmt.Fprintf(out, "gate %d %s: %s\n", index+1, names[index], verdict); err != nil {
			return err
		}
	}
	return nil
}
