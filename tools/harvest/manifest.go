package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"slices"
	"strings"
)

type manifestRow struct {
	Path       string `json:"path"`
	Repository string `json:"repository"`
	Source     string `json:"source"`
	Licence    string `json:"licence"`
	Digest     string `json:"sha256"`
}

func writeCorpus(root string, fixtures []fixture) error {
	wanted := make(map[string]bool, len(fixtures))
	for _, f := range fixtures {
		target := filepath.Join(root, filepath.FromSlash(f.corpusPath))
		wanted[filepath.ToSlash(target)] = true
		if err := writeIfChanged(target, f.content); err != nil {
			return err
		}
	}
	return pruneStale(root, wanted)
}

func writeIfChanged(name string, content []byte) error {
	if existing, err := os.ReadFile(name); err == nil && bytes.Equal(existing, content) {
		return nil
	}
	if err := os.MkdirAll(filepath.Dir(name), 0o755); err != nil {
		return fmt.Errorf("create directory for %s: %w", name, err)
	}
	if err := os.WriteFile(name, content, 0o644); err != nil {
		return fmt.Errorf("write %s: %w", name, err)
	}
	return nil
}

func pruneStale(root string, wanted map[string]bool) error {
	var stale []string
	err := filepath.WalkDir(root, func(name string, entry os.DirEntry, err error) error {
		if err != nil {
			return fmt.Errorf("walk %s: %w", name, err)
		}
		if entry.IsDir() {
			if entry.Name() == cacheDirName {
				return filepath.SkipDir
			}
			return nil
		}
		if !strings.HasSuffix(entry.Name(), ".mmd") || wanted[filepath.ToSlash(name)] {
			return nil
		}
		stale = append(stale, name)
		return nil
	})
	if err != nil {
		return err
	}
	for _, name := range stale {
		if err := os.Remove(name); err != nil {
			return fmt.Errorf("remove stale fixture %s: %w", name, err)
		}
	}
	return nil
}

func manifestRows(fixtures []fixture) []manifestRow {
	rows := make([]manifestRow, 0, len(fixtures))
	for _, f := range fixtures {
		rows = append(rows, manifestRow{
			Path:       f.corpusPath,
			Repository: f.repository,
			Source:     f.source,
			Licence:    f.licence,
			Digest:     digest(f.content),
		})
	}
	slices.SortFunc(rows, func(a, b manifestRow) int { return strings.Compare(a.Path, b.Path) })
	return rows
}

func writeManifest(root string, fixtures []fixture) error {
	data, err := json.MarshalIndent(manifestRows(fixtures), "", manifestIndent)
	if err != nil {
		return fmt.Errorf("encode manifest: %w", err)
	}
	return writeIfChanged(filepath.Join(root, manifestName), append(data, '\n'))
}

func ensureDivergences(root string) error {
	name := filepath.Join(root, divergenceName)
	if _, err := os.Stat(name); err == nil {
		return nil
	}
	return writeIfChanged(name, []byte("[]\n"))
}
