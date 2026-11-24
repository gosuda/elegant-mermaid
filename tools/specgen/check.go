package main

import (
	"crypto/sha256"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"math/big"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
)

var allowedRecipes = []string{
	"gen-check", "go-check", "rust-check", "build", "proofs", "model",
	"oracle", "parity", "kernel-diff", "validate", "lean-parity", "quality",
	"theme-check", "d3-check", "fuzz-smoke", "playground-check",
	"playground-e2e", "wasm-parity", "markdown-parity",
}

var upstreamDetectorIDs = []string{
	"flowchart-elk", "mindmap", "architecture", "agentflow", "c4", "kanban",
	"classDiagram", "er", "gantt", "info", "pie", "requirement", "sequence",
	"swimlane", "flowchart-v2", "timeline", "gitGraph", "stateDiagram",
	"journey", "quadrantChart", "sankey", "packet", "xychart", "block",
	"eventmodeling", "treeView", "radar", "ishikawa", "treemap", "railroad",
	"railroadEbnf", "railroadAbnf", "railroadPeg", "venn", "wardley",
	"cynefin", "usecase",
}

var (
	recipePattern = regexp.MustCompile(`\[just ([a-z0-9-]+)(?::\s*[A-Za-z0-9_]+)?\]\s*$`)
	idPattern     = regexp.MustCompile(`(?:^|[^A-Za-z0-9-])([a-z][a-z0-9]*(?:-[a-z0-9]+)*-[0-9]{2,3})(?:$|[^A-Za-z0-9-])`)
)

type discard struct{}

func (discard) Write(p []byte) (int, error) { return len(p), nil }

func checkRoot(root string, stdout io.Writer) error {
	problems, err := collectProblems(root)
	if err != nil {
		return err
	}
	for _, problem := range problems {
		if _, err := fmt.Fprintln(stdout, problem); err != nil {
			return err
		}
	}
	if len(problems) == 0 {
		_, err = fmt.Fprintln(stdout, "specgen: generated files are current")
		return err
	}
	return fmt.Errorf("%d problem(s)", len(problems))
}

func collectProblems(root string) ([]string, error) {
	in, err := loadInputs(root)
	if err != nil {
		return nil, err
	}
	files, err := buildOutputsFrom(root, in)
	if err != nil {
		return nil, err
	}
	diffProblems, err := compareOutputs(root, files)
	if err != nil {
		return nil, err
	}
	specProblems, err := checkSpecRequirements(root)
	if err != nil {
		return nil, err
	}
	problems := slices.Concat(diffProblems, checkSources(root, in), specProblems, checkDetectorCoverage(in), checkRho(in))
	slices.Sort(problems)
	return problems, nil
}

func checkSources(root string, in *inputs) []string {
	var problems []string
	for _, source := range in.sources {
		data, err := os.ReadFile(filepath.Join(root, filepath.FromSlash(source.Path)))
		if errors.Is(err, os.ErrNotExist) {
			if !strings.HasPrefix(source.Path, ".tools/") {
				problems = append(problems, "source missing: "+source.Path)
			}
			continue
		}
		if err != nil {
			problems = append(problems, fmt.Sprintf("source unreadable: %s: %v", source.Path, err))
			continue
		}
		sum := sha256.Sum256(data)
		actual := hex.EncodeToString(sum[:])
		if actual != strings.ToLower(source.SHA256) {
			problems = append(problems, fmt.Sprintf("source hash differs: %s (want %s, got %s)", source.Path, source.SHA256, actual))
		}
	}
	return problems
}

func checkSpecRequirements(root string) ([]string, error) {
	var problems []string
	seen := make(map[string]string)
	specDir := filepath.Join(root, "spec")
	err := filepath.WalkDir(specDir, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			if errors.Is(err, os.ErrNotExist) {
				return nil
			}
			return err
		}
		if d.IsDir() || !strings.HasSuffix(path, ".md") {
			return nil
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		problems = append(problems, checkRequirementLines(string(data), rel, seen)...)
		return nil
	})
	if err != nil {
		return nil, err
	}
	return problems, nil
}

func checkRequirementLines(text, rel string, seen map[string]string) []string {
	var problems []string
	for lineNo, line := range strings.Split(text, "\n") {
		match := recipePattern.FindStringSubmatch(line)
		if match == nil {
			continue
		}
		recipe := match[1]
		if !slices.Contains(allowedRecipes, recipe) {
			problems = append(problems, fmt.Sprintf("%s:%d: unknown recipe %q", rel, lineNo+1, recipe))
		}
		id := idPattern.FindStringSubmatch(line)
		if id == nil {
			problems = append(problems, fmt.Sprintf("%s:%d: requirement line has no ID", rel, lineNo+1))
			continue
		}
		if first, dup := seen[id[1]]; dup {
			problems = append(problems, fmt.Sprintf("%s:%d: requirement ID %s repeats (first at %s)", rel, lineNo+1, id[1], first))
			continue
		}
		seen[id[1]] = fmt.Sprintf("%s:%d", rel, lineNo+1)
	}
	return problems
}

func checkDetectorCoverage(in *inputs) []string {
	if len(in.kinds) == 0 {
		return nil
	}
	aliases := make(map[string]struct{})
	for _, kind := range in.kinds {
		for _, alias := range kind.Aliases {
			aliases[alias] = struct{}{}
		}
	}
	var problems []string
	for _, id := range upstreamDetectorIDs {
		if _, ok := aliases[id]; !ok {
			problems = append(problems, "detector id missing from kinds.json aliases: "+id)
		}
	}
	return problems
}

func checkRho(in *inputs) []string {
	if len(in.layoutConst) == 0 {
		return nil
	}
	want := rhoQ30()
	var problems []string
	found := false
	for _, c := range in.layoutConst {
		if c.Name != "treemap.rho_q30" {
			continue
		}
		found = true
		if int64(c.Vector) != want || int64(c.Cell) != want {
			problems = append(problems, fmt.Sprintf("treemap.rho_q30 is %d/%d, want %d", c.Vector, c.Cell, want))
		}
	}
	if !found {
		problems = append(problems, "layout-constants.json has no treemap.rho_q30")
	}
	return problems
}

func rhoQ30() int64 {
	five := new(big.Int).Lsh(big.NewInt(5), 60)
	root := integerRoot(five, 2)
	sum := new(big.Int).Add(new(big.Int).Lsh(big.NewInt(1), 30), root)
	sum.Rsh(sum, 1)
	return sum.Int64()
}
