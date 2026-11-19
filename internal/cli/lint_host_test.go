package cli

import (
	"path/filepath"
	"testing"
)

const (
	hostFixture = "# T\n\n> ```mermaid\n> sequenceDiagram\n>   participant \"Bob\n>   A->>Bob: hi\n> ```\n\n```mermaid\nflowchart TD\n  A --> B\n  end\n```\n"
	hostFixed   = "# T\n\n> ```mermaid\n> sequenceDiagram\n>   participant \"Bob\"\n>   A->>Bob: hi\n> ```\n\n```mermaid\nflowchart TD\n  A --> B\n```\n"
)

var hostReports = map[string]string{
	"text":   "doc.md:5:17: warning[sequence/quote-unclosed]: A participant or actor name or alias starts a quote but does not close it\n  |\n5 | >   participant \"Bob\n  |                 ^~~~\n  = help: Close the quote: participant \"Bob\" or participant Alice as \"Alias\"\n  = fix: Insert the closing quote\n\ndoc.md:12:3: error[flowchart/end-without-subgraph]: end appears without a matching subgraph\n   |\n12 |   end\n   |   ^~~\n  = help: Remove this end line, or add a subgraph above it.\n  = fix: Remove the stray end line\n",
	"json":   "{\"version\":1,\"files\":[{\"path\":\"doc.md\",\"kind\":null,\"diagnostics\":[{\"code\":\"sequence/quote-unclosed\",\"severity\":\"warning\",\"message\":\"A participant or actor name or alias starts a quote but does not close it\",\"span\":{\"start\":52,\"end\":56},\"line\":5,\"column\":17,\"end_line\":5,\"end_column\":21,\"related\":[],\"help\":\"Close the quote: participant \\\"Bob\\\" or participant Alice as \\\"Alias\\\"\",\"fixes\":[{\"title\":\"Insert the closing quote\",\"safety\":\"unsafe\",\"edits\":[{\"span\":{\"start\":56,\"end\":56},\"new_text\":\"\\\"\"}]}]},{\"code\":\"flowchart/end-without-subgraph\",\"severity\":\"error\",\"message\":\"end appears without a matching subgraph\",\"span\":{\"start\":116,\"end\":119},\"line\":12,\"column\":3,\"end_line\":12,\"end_column\":6,\"related\":[],\"help\":\"Remove this end line, or add a subgraph above it.\",\"fixes\":[{\"title\":\"Remove the stray end line\",\"safety\":\"unsafe\",\"edits\":[{\"span\":{\"start\":114,\"end\":120},\"new_text\":\"\"}]}]}]}],\"summary\":{\"files\":1,\"errors\":1,\"warnings\":1,\"info\":0}}\n",
	"sarif":  "{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",\"version\":\"2.1.0\",\"runs\":[{\"tool\":{\"driver\":{\"name\":\"emd\",\"version\":\"0.1.0\",\"rules\":[{\"id\":\"flowchart/end-without-subgraph\",\"shortDescription\":{\"text\":\"end appears without a matching subgraph\"},\"help\":{\"text\":\"Remove this end line, or add a subgraph above it.\"}},{\"id\":\"sequence/quote-unclosed\",\"shortDescription\":{\"text\":\"A participant or actor name or alias starts a quote but does not close it\"},\"help\":{\"text\":\"Close the quote: participant \\\"Bob\\\" or participant Alice as \\\"Alias\\\"\"}}]}},\"results\":[{\"ruleId\":\"sequence/quote-unclosed\",\"level\":\"warning\",\"message\":{\"text\":\"A participant or actor name or alias starts a quote but does not close it\"},\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"doc.md\"},\"region\":{\"startLine\":5,\"startColumn\":17,\"endLine\":5,\"endColumn\":21}}}]},{\"ruleId\":\"flowchart/end-without-subgraph\",\"level\":\"error\",\"message\":{\"text\":\"end appears without a matching subgraph\"},\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"doc.md\"},\"region\":{\"startLine\":12,\"startColumn\":3,\"endLine\":12,\"endColumn\":6}}}]}]}]}\n",
	"github": "::warning file=doc.md,line=5,col=17,endLine=5,endColumn=21,title=sequence/quote-unclosed::A participant or actor name or alias starts a quote but does not close it\n::error file=doc.md,line=12,col=3,endLine=12,endColumn=6,title=flowchart/end-without-subgraph::end appears without a matching subgraph\n",
}

func TestLintMarkdownHostFormats(t *testing.T) {
	t.Chdir(writeLintFiles(t, map[string]string{"doc.md": hostFixture}))
	for _, format := range []string{"text", "json", "sarif", "github"} {
		args := []string{"lint", "--no-config", "--color", "never", "--output-format", format, "doc.md"}
		expectInvocation(t, "", args, hostReports[format], "", 1)
	}
}

func TestLintFixMarkdownHostKeepsFenceEdges(t *testing.T) {
	dir := writeLintFiles(t, map[string]string{"doc.md": hostFixture})
	path := filepath.Join(dir, "doc.md")
	if _, _, code := invoke(t, "", "lint", "--fix", "--no-config", path); code != 1 || readText(t, path) != hostFixture {
		t.Fatalf("safe fixes only: exit=%d file=%q", code, readText(t, path))
	}
	expectInvocation(t, "", []string{"lint", "--fix", "--unsafe-fixes", "--no-config", path}, "", "", 0)
	if got := readText(t, path); got != hostFixed {
		t.Fatalf("host after the unsafe fixes: %q; want %q", got, hostFixed)
	}
}
