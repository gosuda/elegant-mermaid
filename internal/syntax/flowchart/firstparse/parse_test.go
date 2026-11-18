package firstparse_test

import (
	"sync"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
	"github.com/stretchr/testify/require"
)

func TestConcurrentFirstParse(t *testing.T) {
	sources := []string{"flowchart TB\nA-->B\n", "flowchart LR\nC-->D\n"}
	const workers = 8
	type parsed struct {
		file  *flowchart.File
		diags []diag.Diagnostic
	}
	results := make([]parsed, workers)
	ready := make(chan struct{})
	start := make(chan struct{})
	var wg sync.WaitGroup
	for w := range workers {
		wg.Go(func() {
			ready <- struct{}{}
			<-start
			file, diags := flowchart.Parse([]byte(sources[w%len(sources)]), nil)
			results[w] = parsed{file: file, diags: diags}
		})
	}
	for range workers {
		<-ready
	}
	close(start)
	wg.Wait()

	for w, res := range results {
		src := sources[w%len(sources)]
		want := [2]string{"A", "B"}
		if w%len(sources) == 1 {
			want = [2]string{"C", "D"}
		}
		require.NotNil(t, res.file, "worker %d %q: nil file", w, src)
		require.Empty(t, res.diags, "worker %d %q: diagnostics %v", w, src, res.diags)
		require.Len(t, res.file.Doc.Lines, 1, "worker %d %q: lines %d", w, src, len(res.file.Doc.Lines))
		stmt, ok := res.file.Doc.Lines[0].Stmt.(*flowchart.VertexStatement)
		require.True(t, ok, "worker %d %q: statement is %T", w, src, res.file.Doc.Lines[0].Stmt)
		require.Len(t, stmt.Groups, 2, "worker %d %q: groups %d", w, src, len(stmt.Groups))
		require.Len(t, stmt.Links, 1, "worker %d %q: links %d", w, src, len(stmt.Links))
		require.Len(t, stmt.Groups[0].Vertices, 1, "worker %d %q: first group has %d vertices", w, src, len(stmt.Groups[0].Vertices))
		require.Len(t, stmt.Groups[1].Vertices, 1, "worker %d %q: second group has %d vertices", w, src, len(stmt.Groups[1].Vertices))
		require.Equal(t, want[0], stmt.Groups[0].Vertices[0].Vertex.ID.String(), "worker %d %q: first endpoint %q", w, src, stmt.Groups[0].Vertices[0].Vertex.ID.String())
		require.Equal(t, want[1], stmt.Groups[1].Vertices[0].Vertex.ID.String(), "worker %d %q: second endpoint %q", w, src, stmt.Groups[1].Vertices[0].Vertex.ID.String())
		require.Equal(t, "-->", stmt.Links[0].Statement.Open.Text, "worker %d %q: link token %q", w, src, stmt.Links[0].Statement.Open.Text)
	}
}
