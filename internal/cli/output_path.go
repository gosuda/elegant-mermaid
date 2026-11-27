package cli

import (
	"os"
	"path/filepath"
)

// Preserve component order: a symlink followed by .. must reach the parent of
// its filesystem target. filepath.Dir and filepath.Join would collapse it first.
func outputDirectory(path string) string {
	directory, _ := filepath.Split(path)
	if directory == "" {
		return "."
	}
	return directory
}

func joinOutputPath(directory, name string) string {
	if directory == "" || directory == "." {
		return name
	}
	if directory == filepath.VolumeName(directory) && !filepath.IsAbs(directory) {
		return directory + name
	}
	if os.IsPathSeparator(directory[len(directory)-1]) {
		return directory + name
	}
	return directory + string(os.PathSeparator) + name
}

