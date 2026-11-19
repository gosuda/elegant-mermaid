package main

import (
	"errors"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strings"
)

const (
	attributionDirectory  = "directory"
	attributionHeader     = "header"
	attributionOutOfScope = "out-of-scope"
	attributionUnknown    = "unknown"
)

func main() {
	summary, err := execute(os.Args[1:], os.Getenv("EMD_BIN"))
	if err != nil {
		fmt.Fprintf(os.Stderr, "harvest: %v\n", err)
		os.Exit(2)
	}
	_, _ = os.Stdout.WriteString(summary)
}

type options struct {
	root     string
	flatKind string
}

func execute(args []string, binaryOverride string) (string, error) {
	return executeSources(args, fixtureSources, binaryOverride)
}

func executeSources(args []string, sources []sourceSpec, binaryOverride string) (string, error) {
	opts, err := parseFlags(args)
	if err != nil {
		return "", err
	}
	if opts.flatKind != "" {
		return flatList(opts.root, opts.flatKind, binaryOverride)
	}
	reg, err := loadRegistry(filepath.Join(opts.root, filepath.FromSlash(kindRegistryPath)))
	if err != nil {
		return "", err
	}
	h := newHarvester(opts.root, reg, sources)
	fixtures, err := h.collect()
	if err != nil {
		return "", err
	}
	corpusRoot := filepath.Join(opts.root, corpusRootName)
	if err := writeCorpus(corpusRoot, fixtures); err != nil {
		return "", err
	}
	if err := writeManifest(corpusRoot, fixtures); err != nil {
		return "", err
	}
	if err := ensureDivergences(corpusRoot); err != nil {
		return "", err
	}
	return h.report(fixtures), nil
}

func parseFlags(args []string) (options, error) {
	opts := options{root: "."}
	for i := 0; i < len(args); i++ {
		arg := args[i]
		value, hasValue := strings.CutPrefix(arg, "-root=")
		switch {
		case arg == "-flat-list":
			if i+1 >= len(args) {
				return options{}, errors.New("flag -flat-list needs a kind")
			}
			i++
			opts.flatKind = args[i]
		case arg == "-root":
			if i+1 >= len(args) {
				return options{}, errors.New("flag -root needs a directory")
			}
			i++
			opts.root = args[i]
		case hasValue:
			opts.root = value
		default:
			return options{}, fmt.Errorf("unknown flag %q; harvest takes -root DIR", arg)
		}
	}
	return opts, nil
}

func (h *harvester) report(fixtures []fixture) string {
	var out strings.Builder
	fmt.Fprintf(&out, "copied %d fixtures into %s/\n", len(fixtures), corpusRootName)
	writeCounts(&out, "source", countBy(fixtures, func(f fixture) string { return f.repository + ": " + sourceLabel(f.source) }))
	writeCounts(&out, "repository", countBy(fixtures, func(f fixture) string { return f.repository }))
	writeCounts(&out, "kind", countBy(fixtures, func(f fixture) string { return kindOf(f.corpusPath) }))
	writeCounts(&out, "filed by", countBy(fixtures, func(f fixture) string { return f.attribution }))
	writeCounts(&out, "e2e", countBy(fixturesWithPrefix(fixtures, "e2e/diagrams/"), func(f fixture) string { return f.attribution }))
	for _, f := range fixtures {
		if kindOf(f.corpusPath) == unknownKind {
			fmt.Fprintf(&out, "  unknown header: %s (from %s/%s)\n", f.corpusPath, f.repository, f.source)
		}
	}
	fmt.Fprint(&out, "notices to add:\n")
	for _, repository := range slices.Sorted(maps.Keys(h.licences)) {
		fmt.Fprintf(&out, "  %s %s %s\n", repository, h.licences[repository], h.licencePath[repository])
	}
	return out.String()
}

func sourceLabel(sourcePath string) string {
	directory, _, found := strings.Cut(sourcePath, "/")
	if !found {
		return "root"
	}
	return directory
}

func fixturesWithPrefix(fixtures []fixture, prefix string) []fixture {
	var out []fixture
	for _, f := range fixtures {
		if strings.HasPrefix(f.source, prefix) {
			out = append(out, f)
		}
	}
	return out
}

func writeCounts(out *strings.Builder, label string, counts map[string]int) {
	for _, key := range slices.Sorted(maps.Keys(counts)) {
		fmt.Fprintf(out, "  %s %-24s %5d\n", label, key, counts[key])
	}
}

func countBy(fixtures []fixture, key func(fixture) string) map[string]int {
	counts := make(map[string]int, len(fixtures))
	for _, f := range fixtures {
		counts[key(f)]++
	}
	return counts
}

func kindOf(corpusPath string) string {
	kind, _, _ := strings.Cut(corpusPath, "/")
	return kind
}
