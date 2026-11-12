package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"io/fs"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"slices"
	"strings"
	"sync"
)

type flatModel struct {
	Boxes  []struct{ ID, Role, Parent string }
	Routes []struct{ ID, From, To string }
	Labels []struct{ Owner string }
}

type flatResult struct {
	reason string
	err    error
}

func flatList(root, kind string) (string, error) {
	if filepath.Base(kind) != kind || slices.Contains([]string{"", ".", "..", "_out-of-scope"}, kind) {
		return "", fmt.Errorf("invalid flat-list kind %q", kind)
	}
	binary, err := flatBinary(root)
	if err != nil {
		return "", err
	}
	paths, err := flatPaths(root, kind)
	if err != nil {
		return "", err
	}
	results := inspectFlatFiles(root, binary, paths)
	var out strings.Builder
	for i, result := range results {
		if result.err != nil {
			return "", fmt.Errorf("%s: %w", paths[i], result.err)
		}
		if result.reason == "" {
			out.WriteString(paths[i])
			out.WriteByte('\n')
		}
	}
	return out.String(), nil
}

func flatBinary(root string) (string, error) {
	binary := os.Getenv("EMD_BIN")
	if binary == "" {
		binary = filepath.Join("bin", "emd-go")
	}
	if !filepath.IsAbs(binary) {
		binary = filepath.Join(root, binary)
	}
	binary, err := filepath.Abs(binary)
	if err != nil {
		return "", err
	}
	if _, err := exec.LookPath(binary); err != nil {
		return "", fmt.Errorf("flat-list binary %s unavailable; run just build: %w", binary, err)
	}
	return binary, nil
}

func flatPaths(root, kind string) ([]string, error) {
	var paths []string
	err := filepath.WalkDir(filepath.Join(root, "corpus", kind), func(path string, entry fs.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if entry.IsDir() || filepath.Ext(path) != ".mmd" {
			return nil
		}
		relative, err := filepath.Rel(root, path)
		if err != nil {
			return err
		}
		paths = append(paths, filepath.ToSlash(relative))
		return nil
	})
	slices.Sort(paths)
	return paths, err
}

func inspectFlatFiles(root, binary string, paths []string) []flatResult {
	results := make([]flatResult, len(paths))
	jobs := make(chan int)
	var workers sync.WaitGroup
	for range min(8, runtime.GOMAXPROCS(0)) {
		workers.Go(func() {
			for i := range jobs {
				results[i] = inspectFlatFile(root, binary, paths[i])
			}
		})
	}
	for i := range paths {
		jobs <- i
	}
	close(jobs)
	workers.Wait()
	return results
}

func inspectFlatFile(root, binary, path string) flatResult {
	data, err := exec.Command(binary, "check", "--output-format", "json", filepath.Join(root, filepath.FromSlash(path))).Output()
	var status *exec.ExitError
	if err != nil && !errors.As(err, &status) {
		return flatResult{err: err}
	}
	var check struct{ Summary struct{ Errors *int } }
	if decodeErr := json.Unmarshal(data, &check); decodeErr != nil {
		return flatResult{err: fmt.Errorf("decode check: %w", decodeErr)}
	}
	if check.Summary.Errors == nil {
		return flatResult{err: errors.New("check output has no summary.errors")}
	}
	if err != nil || *check.Summary.Errors != 0 {
		return flatResult{reason: "rejected"}
	}
	data, err = exec.Command(binary, "layout", "--stage", "model", "--profile", "cell", filepath.Join(root, filepath.FromSlash(path))).Output()
	if err != nil {
		return flatResult{err: fmt.Errorf("model dump: %w", err)}
	}
	var model flatModel
	if err := json.Unmarshal(data, &model); err != nil {
		return flatResult{err: fmt.Errorf("decode model: %w", err)}
	}
	return flatResult{reason: flatReason(model)}
}

func flatReason(model flatModel) string {
	for _, box := range model.Boxes {
		if box.Role != "node" {
			return "group"
		}
		if box.Parent != "" {
			return "nested"
		}
	}
	routes := make(map[string]bool, len(model.Routes))
	for _, route := range model.Routes {
		if route.From == route.To {
			return "self-loop"
		}
		routes[route.ID] = true
	}
	for _, label := range model.Labels {
		if routes[label.Owner] {
			return "edge-label"
		}
	}
	if flatCycle(model) {
		return "cycle"
	}
	return ""
}

func flatCycle(model flatModel) bool {
	indices := make(map[string]int, len(model.Boxes))
	for i, box := range model.Boxes {
		indices[box.ID] = i
	}
	degree := make([]int, len(model.Boxes))
	edges := make([][]int, len(model.Boxes))
	for _, route := range model.Routes {
		from, fromOK := indices[route.From]
		to, toOK := indices[route.To]
		if !fromOK || !toOK {
			return true
		}
		edges[from] = append(edges[from], to)
		degree[to]++
	}
	var ready []int
	for i, count := range degree {
		if count == 0 {
			ready = append(ready, i)
		}
	}
	for i := 0; i < len(ready); i++ {
		for _, to := range edges[ready[i]] {
			degree[to]--
			if degree[to] == 0 {
				ready = append(ready, to)
			}
		}
	}
	return len(ready) != len(model.Boxes)
}
