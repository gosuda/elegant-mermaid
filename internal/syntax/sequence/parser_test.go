package sequence

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
)

func parse(src string) (*Start, []diag.Diagnostic) {
	return Parse([]byte(src), nil)
}

func kinds(src string) []string {
	start, _ := parse(src)
	var out []string
	for _, line := range start.Document.Lines {
		if line.Statement == nil {
			continue
		}
		out = append(out, kindName(line.Statement.Kind))
	}
	return out
}

func kindName(kind StatementKind) string {
	name := fmt.Sprintf("%T", kind)
	return strings.ToLower(name[strings.LastIndexByte(name, '.')+1:])
}

func codes(src string) []string {
	_, ds := parse(src)
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func tokenKinds(src string) []string {
	var out []string
	for _, token := range lex(src, nil) {
		out = append(out, token.Kind)
	}
	return out
}

func TestLexesArrowTokensInTableOrder(t *testing.T) {
	require.Contains(t, tokenKinds("A->>B: x\n"), "SOLID_ARROW")
	require.NotContains(t, tokenKinds("A->>B: x\n"), "DOTTED_ARROW")
	require.Contains(t, tokenKinds("A/|--B: x\n"), "SOLID_ARROW_TOP_REVERSE_DOTTED")
}

func TestKeywordsFoldCaseAndEndAtBoundary(t *testing.T) {
	require.Equal(t, []string{"controlblock"}, kinds("sequenceDiagram\nLOOP every day\nA->>B: x\nEND\n"))
	require.Equal(t, []string{"signal"}, kinds("sequenceDiagram\nNotes->>B: x\n"))
	require.Equal(t, []string{"controlblock"}, kinds("sequenceDiagram\npar_over X\nEND\n"))
	require.Equal(t, []string{"controlblock"}, kinds("sequenceDiagram\ncritical X\noption Y\nend\n"))
	require.Equal(t, []string{"signal"}, kinds("sequenceDiagram\nendpoint->>B: x\n"))
	require.Equal(t, []string{"signal"}, kinds("sequenceDiagram\nLink->>B: x\n"))
	require.Equal(t, []string{"link"}, kinds("sequenceDiagram\nlink A: Dashboard @ https://x.dev\n"))
	require.Equal(t, []string{"sequence/unknown-statement", "sequence/unknown-statement"}, codes("sequenceDiagram\noption X\nend\n"))
}

func TestStrayInvalidTokenIsABlankLine(t *testing.T) {
	_, ds := parse("sequenceDiagram\n<\nA->>B: x\n")
	require.Empty(t, ds)
}

func TestInvalidParticipantIDIsRejected(t *testing.T) {
	require.Equal(t, []string{"sequence/unexpected-token"}, codes("sequenceDiagram\nparticipant a<b\n"))
}

func TestBoxBodyAcceptsParticipantsOnly(t *testing.T) {
	require.Empty(t, codes("sequenceDiagram\nbox X\nparticipant A\ndestroy B\nend\n"))
	require.Equal(t, []string{"sequence/unknown-statement"}, codes("sequenceDiagram\nbox X\ncreate participant A\nend\n"))
}

func TestAccessibilityFormsCaptureValues(t *testing.T) {
	src := "sequenceDiagram\naccTitle: T\naccDescr: D\naccDescr {\nmulti\n}\naccDescr {}\nA->>B: x\n"
	_, ds := parse(src)
	require.Empty(t, ds)
	require.Equal(t, []string{"accessibility", "accessibility", "accessibility", "signal"}, kinds(src))
}

func TestUnterminatedMetadataAndAccessibilityReportTheirOpener(t *testing.T) {
	src := "sequenceDiagram\nparticipant A@{ \"type\": \"actor\"\n"
	_, ds := parse(src)
	require.Len(t, ds, 1)
	require.Equal(t, "sequence/unterminated", ds[0].Code)
	require.Equal(t, "@{ \"type\": \"actor\"\n", src[ds[0].Span.Start:ds[0].Span.End])
	src = "sequenceDiagram\naccDescr {\nnever closed\n"
	_, ds = parse(src)
	require.Len(t, ds, 1)
	require.Equal(t, "sequence/unterminated", ds[0].Code)
	require.Equal(t, strings.Index(src, "accDescr"), ds[0].Span.Start)
}

func TestLeftOfAndActorSplit(t *testing.T) {
	names := tokenKinds("note left of Alice: hi\n")
	require.Contains(t, names, "left_of")
	require.Contains(t, names, "note")
}

func TestActorStopsBeforeArrowAndParens(t *testing.T) {
	actors := func(src string) []string {
		var out []string
		for _, token := range lex(src, nil) {
			if token.Kind == "ACTOR" {
				out = append(out, token.Text)
			}
		}
		return out
	}
	require.Equal(t, []string{"A", "B"}, actors("A->>B: hi\n"))
	require.Contains(t, tokenKinds("A()->>B: hi\n"), "()")
	require.Equal(t, []string{"A", "B"}, actors("A()->>B: hi\n"))
}

func TestNewlineAndSemicolonBothTerminate(t *testing.T) {
	require.Equal(t, []string{"signal", "signal"}, kinds("sequenceDiagram\nA->>B: x; C->>D: y\n"))
}

func TestParticipantModesCaptureAliasAndConfig(t *testing.T) {
	_, ds := parse("sequenceDiagram\nparticipant Bob as Bob Marley\nA->>Bob: hi\n")
	require.Empty(t, ds)
	_, ds = parse("sequenceDiagram\nparticipant Bob@{ \"type\": \"actor\" } as Bobby\nA->>Bob: hi\n")
	require.Empty(t, ds)
}

func TestUnterminatedBlockReportsOnce(t *testing.T) {
	require.Equal(t, []string{"sequence/unterminated"}, codes("sequenceDiagram\nloop every day\nA->>B: x\n"))
	require.Equal(t, []string{"sequence/unterminated"}, codes("sequenceDiagram\nbox Tan\nparticipant X\n"))
}

func TestRecoveryPreservesEnclosingBlock(t *testing.T) {
	src := "sequenceDiagram\nloop L\nA->>: x\nB->>C: y\nend\nD->>E: z\n"
	_, ds := parse(src)
	require.Len(t, ds, 1)
	require.Equal(t, "sequence/unexpected-token", ds[0].Code)
	require.Equal(t, ": x", src[ds[0].Span.Start:ds[0].Span.End])
	require.Equal(t, []string{"controlblock", "signal"}, kinds(src))
}

func TestUnknownStatementStartsNoProduction(t *testing.T) {
	require.Equal(t, []string{"sequence/unknown-statement"}, codes("sequenceDiagram\noff x\n"))
}

func TestNestingLimitStopsRecursion(t *testing.T) {
	src := "sequenceDiagram\n" + strings.Repeat("loop L\n", 65) + strings.Repeat("end\n", 65)
	require.Contains(t, codes(src), "limit/nesting-depth")
}

func TestAccessibilitiesCaptureValues(t *testing.T) {
	_, ds := parse("sequenceDiagram\naccTitle: My title\naccDescr { multi line } \nA->>B: x\n")
	require.Empty(t, ds)
}

func TestStatementSpansExcludeTerminator(t *testing.T) {
	src := "sequenceDiagram\nA->>B: hi\n"
	start, _ := parse(src)
	for _, line := range start.Document.Lines {
		if line.Statement != nil {
			require.Equal(t, "\n", src[line.Statement.Span.End:])
			return
		}
	}
	t.Fatal("signal statement missing")
}

func ownSpan(kind StatementKind) (source.Span, bool) {
	switch node := kind.(type) {
	case *Autonumber:
		return node.Span, true
	case *Activate:
		return node.Span, true
	case *Deactivate:
		return node.Span, true
	}
	return source.Span{}, false
}

func TestEveryStatementSpanStopsBeforeItsTerminator(t *testing.T) {
	src := "sequenceDiagram\nbox B\nparticipant P\ndestroy P\nend\nparticipant A\nactor C\ncreate participant D\nautonumber 3\nactivate A\ndeactivate A\nNote over A: x\nlink A: l @ u\nlinks A: {}\nproperties A: {}\ndetails A: {}\nA->>C: hi\n"
	start, ds := parse(src)
	require.Empty(t, ds)
	seen := 0
	var check func(lines []Line)
	check = func(lines []Line) {
		for _, line := range lines {
			if line.Statement == nil {
				continue
			}
			seen++
			span := line.Statement.Span
			require.Equal(t, span, line.Span)
			require.Equal(t, "\n", src[span.End:span.End+1], "statement %q", src[span.Start:span.End])
			if own, ok := ownSpan(line.Statement.Kind); ok {
				require.Equal(t, span, own)
			}
			if box, ok := line.Statement.Kind.(*BoxBlock); ok {
				check(box.Section.Lines)
				require.Equal(t, box.Section.Lines[len(box.Section.Lines)-1].Span.End, box.Section.Span.End)
			}
		}
	}
	check(start.Document.Lines)
	require.Equal(t, 15, seen)
	last := start.Document.Lines[len(start.Document.Lines)-1]
	require.Equal(t, last.Span.End, start.Document.Span.End)
}
