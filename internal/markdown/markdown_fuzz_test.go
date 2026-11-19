package markdown

import "testing"

func FuzzExtract(f *testing.F) {
	for _, s := range []string{"", "```mermaid\nx\n```\n", "> - x\n>   ```mermaid\n>   flowchart LR\n>     A --> B\n>   ```\n", "-\tx\n\t~~~mmd\n\tx\n\t~~~\n"} {
		f.Add([]byte(s))
	}
	f.Fuzz(func(t *testing.T, host []byte) {
		for _, b := range Blocks(host) {
			checkMapping(t, host, b)
		}
	})
}
