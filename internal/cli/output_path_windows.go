package cli

import (
	"errors"
	"os"
	"path/filepath"
	"slices"
	"strings"
	"syscall"

	"golang.org/x/sys/windows"
)

// Keep canonical ancestors literal. Only components still supplied by an
// ordinary operand receive Win32 normalization. Resolve links before parents.
func resolvedOutputDirectory(path string) (string, error) {
	if path == "" {
		path = "."
	}
	literal := literalWindowsOutputPath(path)
	if literal && !filepath.IsAbs(path) {
		return "", windows.ERROR_INVALID_NAME
	}
	base, suffix, err := windowsOutputBase(path)
	if err != nil {
		return "", err
	}
	parts := strings.FieldsFunc(suffix, func(character rune) bool {
		return character == '\\' || !literal && character == '/'
	})
	parts = slices.DeleteFunc(parts, func(part string) bool { return part == "." })
	for index, name := range parts {
		base, err = resolveWindowsOutputComponent(base, name, literal, index == len(parts)-1)
		if err != nil {
			return "", err
		}
	}
	return base, nil
}

// A drive-relative operand uses that drive's current directory. Root-relative
// operands use the current volume; neither operation cleans the operand suffix.
func windowsOutputBase(path string) (string, string, error) {
	volume := filepath.VolumeName(path)
	suffix := path[len(volume):]
	rooted := filepath.IsAbs(path) || len(suffix) > 0 && os.IsPathSeparator(suffix[0])
	if !rooted {
		base, err := filepath.Abs(volume + ".")
		if err != nil {
			return "", "", err
		}
		resolved, err := canonicalWindowsOutputDirectory(base)
		return resolved, suffix, err
	}
	if volume == "" {
		current, err := os.Getwd()
		if err != nil {
			return "", "", err
		}
		volume = filepath.VolumeName(current)
	}
	base, err := canonicalWindowsOutputDirectory(volume + string(os.PathSeparator))
	return base, suffix, err
}

// Resolve each component before interpreting the next parent component.
// A dangling link is an error, while a genuinely missing directory is a
// prospective creation target whose spelling is already normalized.
func resolveWindowsOutputComponent(base, name string, literal, last bool) (string, error) {
	if name == ".." {
		return filepath.Dir(base), nil
	}
	if !literal {
		normalized, err := normalizedWindowsOutputComponent(name, last)
		if err != nil {
			return "", err
		}
		name = normalized
	}
	if name == "" {
		return base, nil
	}
	next := joinOutputPath(base, name)
	if _, err := os.Lstat(next); errors.Is(err, os.ErrNotExist) {
		return next, nil
	} else if err != nil {
		return "", err
	}
	return canonicalWindowsOutputDirectory(next)
}

// The final entry is not opened: the atomic writer replaces it, including a
// symlink. Its ordinary spelling must still name the same entry in the URL.
func resolvedOutputTarget(path string) (string, error) {
	directory, err := resolvedOutputDirectory(outputDirectory(path))
	if err != nil {
		return "", err
	}
	name := filepath.Base(path)
	if !literalWindowsOutputPath(path) {
		name, err = normalizedWindowsOutputComponent(name, true)
		if err != nil {
			return "", err
		}
	}
	if name == "" || name == "." || name == ".." {
		return "", syscall.EISDIR
	}
	return joinOutputPath(directory, name), nil
}

func literalWindowsOutputPath(path string) bool {
	return strings.HasPrefix(path, "\\\\?\\") || strings.HasPrefix(path, "\\\\.\\")
}

// A synthetic ancestor keeps native lexical normalization away from a real
// canonical directory. The sentinel preserves intermediate-component behavior:
// Win32 does not trim an intermediate trailing space as it trims a final one.
func normalizedWindowsOutputComponent(name string, last bool) (string, error) {
	const root = "C:\\__emd_component__"
	const sentinel = "__emd_following__"
	probe := root + "\\" + name
	if !last {
		probe += "\\" + sentinel
	}
	resolved, err := filepath.Abs(probe)
	if err != nil {
		return "", err
	}
	if !last {
		directory, leaf := filepath.Split(resolved)
		if leaf != sentinel {
			return "", windows.ERROR_INVALID_NAME
		}
		resolved = directory
	}
	relative, err := filepath.Rel(root, resolved)
	if err != nil {
		return "", err
	}
	if relative == "." {
		return "", nil
	}
	if relative == ".." || strings.ContainsAny(relative, "\\/") {
		return "", windows.ERROR_INVALID_NAME
	}
	return relative, nil
}

// Open for metadata rather than directory enumeration, and retain the exact
// handle's canonical spelling. Reopening an ordinary spelling can select a
// different directory when literal and trimmed names both exist.
func canonicalWindowsOutputDirectory(path string) (result string, err error) {
	name, err := windows.UTF16PtrFromString(path)
	if err != nil {
		return "", err
	}
	handle, err := windows.CreateFile(
		name, 0, windows.FILE_SHARE_READ|windows.FILE_SHARE_WRITE|windows.FILE_SHARE_DELETE,
		nil, windows.OPEN_EXISTING, windows.FILE_FLAG_BACKUP_SEMANTICS, 0,
	)
	if err != nil {
		return "", err
	}
	defer func() {
		closeErr := windows.CloseHandle(handle)
		if err == nil {
			err = closeErr
		}
	}()
	var info windows.ByHandleFileInformation
	if err = windows.GetFileInformationByHandle(handle, &info); err != nil {
		return "", err
	}
	if info.FileAttributes&windows.FILE_ATTRIBUTE_DIRECTORY == 0 {
		return "", syscall.ENOTDIR
	}
	return windowsCanonicalOutputPath(handle)
}

func windowsCanonicalOutputPath(handle windows.Handle) (string, error) {
	buffer := make([]uint16, 260)
	for {
		length, callErr := windows.GetFinalPathNameByHandle(handle, &buffer[0], uint32(len(buffer)), 0)
		if callErr != nil {
			return "", callErr
		}
		if uint64(length) < uint64(len(buffer)) {
			return windows.UTF16ToString(buffer[:length]), nil
		}
		capacity := uint64(length) + 1
		if capacity > uint64(^uint32(0)) || capacity > uint64(^uint(0)>>1)/2 {
			return "", windows.ERROR_FILENAME_EXCED_RANGE
		}
		buffer = make([]uint16, int(capacity))
	}
}
