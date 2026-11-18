package cynefin

import (
	"strings"

	"github.com/gosuda/elegant-mermaid/internal/syntax/langium"
)

var DomainNames = []string{"complex", "complicated", "clear", "chaotic", "confusion"}

var grammar = langium.Grammar{
	Keywords: []langium.Keyword{{Text: "cynefin-beta:"}, {Text: "cynefin-beta", Guard: true}, {Text: "-->"}, {Text: ":"}},
	Locals:   []langium.Terminal{{Kind: "DOMAIN_NAME", Match: domainLength}},
}

func domainLength(rest string) int {
	for _, name := range DomainNames {
		if strings.HasPrefix(rest, name) {
			return len(name)
		}
	}
	return 0
}
