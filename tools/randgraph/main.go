package main

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/gosuda/elegant-mermaid/tools/randgraph/gen"
)

const casesPerFamily = 2000

func main() {
	for _, family := range gen.Families() {
		if err := writeFamily(family); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
}

func writeFamily(family string) error {
	dir := filepath.Join("corpus", ".cache", "random", family)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		return err
	}
	list := make([]string, 0, casesPerFamily)
	for i := range casesPerFamily {
		text, err := gen.Source(family, i)
		if err != nil {
			return err
		}
		name := fmt.Sprintf("%04d.mmd", i)
		if err := os.WriteFile(filepath.Join(dir, name), []byte(text), 0o644); err != nil {
			return err
		}
		list = append(list, filepath.ToSlash(filepath.Join(dir, name)))
	}
	index := filepath.Join("corpus", ".cache", "random", family+".txt")
	return os.WriteFile(index, []byte(strings.Join(list, "\n")+"\n"), 0o644)
}
