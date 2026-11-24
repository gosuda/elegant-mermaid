package main

type testCase struct {
	name                 string
	format               string
	args                 []string
	code                 int
	files, links, images map[string]string
	hosts                map[string]string
	absent               []string
}

const first = "```mermaid\nflowchart LR\nA --> B\n```\n"
const second = "~~~mmd\nflowchart TD\nC --> D\n~~~\n"

func cases() []testCase {
	fixtures := imageCases()
	return append(fixtures, hostCases()...)
}

func imageCases() []testCase {
	var fixtures []testCase
	for _, format := range []struct{ extension, prefix string }{
		{"svg", "<svg"}, {"png", "\x89PNG\r\n\x1a\n"}, {"txt", ""},
	} {
		fixtures = append(fixtures, testCase{
			name:   "images-" + format.extension,
			format: format.extension,
			args:   []string{"-o", "output." + format.extension},
			files:  map[string]string{"input.md": first + second},
			images: map[string]string{"output-1." + format.extension: format.prefix, "output-2." + format.extension: format.prefix},
			absent: []string{"output." + format.extension},
		}, testCase{
			name:   "dotfile-" + format.extension,
			format: format.extension,
			args:   []string{"-o", "." + format.extension},
			files:  map[string]string{"input.md": first},
			images: map[string]string{"." + format.extension + "-1": format.prefix},
		})
	}
	return append(fixtures,
		testCase{
			name: "unused-image-parent", args: []string{"-o", "report/image.svg", "-a", "assets"},
			files:  map[string]string{"input.md": first, "report": "unrelated file"},
			images: map[string]string{"assets/image-1.svg": "<svg"},
		},
		testCase{
			name: "symlink-before-parent", args: []string{"-a", "current/../assets", "-e", "svg"},
			files:  map[string]string{"input.md": first, "assets/input-1.svg": "unrelated asset", "releases/v1/keep": "release"},
			links:  map[string]string{"current": "releases/v1"},
			images: map[string]string{"releases/assets/input-1.svg": "<svg"},
		},
		testCase{
			name: "later-invalid-block", args: []string{"-o", "out.svg"}, code: 1,
			files:  map[string]string{"input.md": first + "```mermaid\nflowchart\nA -> B\n```\n", "out-1.svg": "existing image"},
			absent: []string{"out-2.svg"},
		},
	)
}

func hostCases() []testCase {
	fixtures := []testCase{
		{
			name: "raw-host-spans", args: []string{"-o", "docs/out.mdx", "-a", "assets/a b#%()é"},
			files:  map[string]string{"input.md": "Before\xff\r\n> - ```mermaid\r\n>   flowchart LR\r\n>   accTitle: Title [safe] & more!\r\n>   A --> B\r\n>   ```\r\nForeign\xfe\r\n```rust\nlet x = 1;\n```\n" + second},
			images: map[string]string{"assets/a b#%()é/out-1.svg": "<svg", "assets/a b#%()é/out-2.svg": "<svg"},
			hosts:  map[string]string{"docs/out.mdx": "Before\xff\r\n> - ![Title \\[safe\\] \\& more\\!](../assets/a%20b%23%25%28%29%C3%A9/out-1.svg)\r\nForeign\xfe\r\n```rust\nlet x = 1;\n```\n![diagram](../assets/a%20b%23%25%28%29%C3%A9/out-2.svg)\n"},
		},
		{
			name: "host-symlink-parent", args: []string{"-o", "current/out.md", "-a", "assets"},
			files:  map[string]string{"input.md": first, "releases/v1/keep": "release"},
			links:  map[string]string{"current": "releases/v1"},
			images: map[string]string{"assets/out-1.svg": "<svg"},
			hosts:  map[string]string{"releases/v1/out.md": "![diagram](../../assets/out-1.svg)\n"},
		},
		{
			name: "default-assets-symlink-parent", args: []string{"-o", "current/../out.md"},
			files:  map[string]string{"input.md": first, "releases/v1/keep": "release", "out.assets/out-1.svg": "unrelated asset"},
			links:  map[string]string{"current": "releases/v1"},
			images: map[string]string{"releases/out.assets/out-1.svg": "<svg"},
			hosts:  map[string]string{"releases/out.md": "![diagram](out.assets/out-1.svg)\n"},
		},
		{
			name: "missing-directories-final-symlink", args: []string{"-o", "docs/missing/../out.md", "-a", "assets/missing/.."},
			files:  map[string]string{"input.md": first, "sentinel": "unrelated file", "assets/keep": "keep"},
			links:  map[string]string{"assets/out-1.svg": "../sentinel"},
			images: map[string]string{"assets/out-1.svg": "<svg"},
			hosts:  map[string]string{"docs/out.md": "![diagram](../assets/out-1.svg)\n"},
		},
	}
	fixtures = append(fixtures, testCase{
		name: "missing-prefix-before-symlink", args: []string{"-o", "missing/../current/../out.md", "-a", "assets"},
		files:  map[string]string{"input.md": first, "releases/v1/keep": "release"},
		links:  map[string]string{"current": "releases/v1"},
		images: map[string]string{"assets/out-1.svg": "<svg"},
		hosts:  map[string]string{"releases/out.md": "![diagram](../assets/out-1.svg)\n"},
	}, testCase{
		name: "missing-asset-prefix-before-symlink", args: []string{"-o", "docs/out.md", "-a", "missing/../current/../assets"},
		files:  map[string]string{"input.md": first, "releases/v1/keep": "release", "assets/out-1.svg": "unrelated asset"},
		links:  map[string]string{"current": "releases/v1"},
		images: map[string]string{"releases/assets/out-1.svg": "<svg"},
		hosts:  map[string]string{"docs/out.md": "![diagram](../releases/assets/out-1.svg)\n"},
	})
	for _, directory := range []string{"file/..", "dangling/..", "missing/../file/images"} {
		fixtures = append(fixtures, testCase{
			name: "invalid-directory-" + directory, args: []string{"-o", "out.md", "-a", directory}, code: 2,
			files:  map[string]string{"input.md": first, "file": "regular file", "out.md": "existing host"},
			links:  map[string]string{"dangling": "absent"},
			absent: []string{"out-1.svg", "absent", "missing"},
		})
	}
	return fixtures
}
