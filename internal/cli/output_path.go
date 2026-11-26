package cli

import (
	"errors"
	"os"
	"path/filepath"
	"syscall"
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

// Resolve directories before encoding a relative URL. Missing directories are
// prospective mkdir targets; existing links and non-directories retain their
// filesystem meaning. The final output filename is deliberately not resolved.
func resolvedOutputDirectory(path string) (string, error) {
	path, err := absoluteOutputDirectory(path)
	if err != nil {
		return "", err
	}
	return resolveOutputDirectory(path)
}

func absoluteOutputDirectory(path string) (string, error) {
	if filepath.IsAbs(path) {
		return path, nil
	}
	volume := filepath.VolumeName(path)
	base, err := filepath.Abs(volume + ".")
	if err != nil {
		return "", err
	}
	base, err = filepath.EvalSymlinks(base)
	if err != nil {
		return "", err
	}
	if len(path) > len(volume) && os.IsPathSeparator(path[len(volume)]) {
		base = filepath.VolumeName(base)
	}
	return joinOutputPath(base, path[len(volume):]), nil
}

func resolveOutputDirectory(path string) (string, error) {
	if path == "" {
		path = "."
	}
	volume := len(filepath.VolumeName(path))
	for len(path) > volume+1 && os.IsPathSeparator(path[len(path)-1]) {
		path = path[:len(path)-1]
	}
	info, err := os.Stat(path)
	if err == nil {
		if !info.IsDir() {
			return "", syscall.ENOTDIR
		}
		resolved, err := filepath.EvalSymlinks(path)
		if err != nil {
			return "", err
		}
		return filepath.Abs(resolved)
	}
	if !errors.Is(err, os.ErrNotExist) {
		return "", err
	}
	return missingOutputDirectory(path, err)
}

func missingOutputDirectory(path string, notExist error) (string, error) {
	if _, linkErr := os.Lstat(path); linkErr == nil {
		return "", notExist // A dangling link is not a missing directory to create.
	} else if !errors.Is(linkErr, os.ErrNotExist) {
		return "", linkErr
	}
	parent, name := filepath.Split(path)
	if name == "" {
		return "", notExist
	}
	resolved, err := resolveOutputDirectory(parent)
	if err != nil {
		return "", err
	}
	return inspectResolvedDirectory(filepath.Join(resolved, name))
}

// A missing prefix may have been cancelled by .., exposing an existing link or
// file. Inspect that component again before resolving the next one.
func inspectResolvedDirectory(path string) (string, error) {
	if _, err := os.Lstat(path); errors.Is(err, os.ErrNotExist) {
		return path, nil
	} else if err != nil {
		return "", err
	}
	return resolveOutputDirectory(path)
}
