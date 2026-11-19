package sequence

import (
	"slices"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
	syn "github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
)

func resolveSource(src string) (*Model, []diag.Diagnostic) {
	prep := syntax.Preprocess([]byte(src))
	document, _ := syn.Parse([]byte(src), prep.Removed)
	return Resolve([]byte(src), document)
}

func codes(ds []diag.Diagnostic) []string {
	out := make([]string, len(ds))
	for i, d := range ds {
		out[i] = d.Code
	}
	return out
}

func TestColourFunctionRunsToTheLastParenthesis(t *testing.T) {
	color, label, ok := boxColorLabel("rgb(23, 124, 207) Profiles")
	require.True(t, ok)
	require.Equal(t, "rgb(23, 124, 207)", color)
	require.Equal(t, "Profiles", label)
	color, label, ok = boxColorLabel("rgb (1, 2, 3) T")
	require.True(t, ok)
	require.Equal(t, "rgb (1, 2, 3)", color)
	require.Equal(t, "T", label)
}

func TestNamedColourIsTheLeadingWord(t *testing.T) {
	color, label, ok := boxColorLabel("Green New serwis")
	require.True(t, ok)
	require.Equal(t, "Green", color)
	require.Equal(t, "New serwis", label)
	color, label, ok = boxColorLabel("Aqua")
	require.True(t, ok)
	require.Equal(t, "Aqua", color)
	require.Empty(t, label)
}

func TestOtherTextIsTheWholeTitle(t *testing.T) {
	for _, raw := range []string{"Group 1", `"Group"`, "rgb(1,2", "#fff Title"} {
		_, label, ok := boxColorLabel(raw)
		require.False(t, ok, raw)
		require.Equal(t, raw, label)
	}
}

func TestNamedColoursAreSortedForBinarySearch(t *testing.T) {
	require.True(t, slices.IsSorted(namedColors))
}

func TestEntitiesDecodeNumbersAndNames(t *testing.T) {
	require.Equal(t, "A\u00bd#nope; #;", syntax.DecodeEntities("A#frac12;#nope; #;"))
	require.Equal(t, "é", syntax.DecodeEntities("#233;"))
	require.Equal(t, "#0;", syntax.DecodeEntities("#0;"))
}

func TestAutonumberFormatsHundredths(t *testing.T) {
	require.Equal(t, "1", formatNumber(100))
	require.Equal(t, "1.5", formatNumber(150))
	require.Equal(t, "1.25", formatNumber(125))
	value, ok := hundredths("2.505")
	require.True(t, ok)
	require.Equal(t, int64(250), value)
	_, ok = hundredths(".5")
	require.False(t, ok)
}

func TestParticipantsKeepFirstInsertionOrder(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nB->>A: x\nparticipant A as Alpha\nactor C\n")
	require.Empty(t, ds)
	require.Len(t, model.Actors, 3)
	require.Equal(t, "B", model.Actors[0].ID)
	require.Equal(t, "Alpha", model.Actors[1].Label)
	require.Equal(t, "actor", model.Actors[2].Kind)
}

func TestMetadataSelectsDrawKind(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nparticipant Q@{ \"type\": \"queue\" }\nparticipant U@{ \"type\": \"unknown\" }\n")
	require.Empty(t, ds)
	require.Equal(t, "queue", model.Actors[0].Kind)
	require.Equal(t, "participant", model.Actors[1].Kind)
}

func TestMetadataAliasAndPropertiesComeFromYAMLMapping(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nparticipant R@{ alias: Jobs }\nparticipant S@{ x: 1 }\nparticipant L@{ label: Kept }\n")
	require.Empty(t, ds)
	require.Equal(t, "Jobs", model.Actors[0].Label)
	require.Equal(t, []Pair{{Key: "x", Value: "1"}}, model.Actors[1].Properties)
	require.Equal(t, "L", model.Actors[2].Label, "only the alias key renames a participant")
	require.Equal(t, []Pair{{Key: "label", Value: "Kept"}}, model.Actors[2].Properties)
}

func TestMetadataOnOneLineHoldsSeveralCommaSeparatedKeys(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nparticipant API@{ \"type\": \"boundary\", \"alias\": \"Public API\", \"x\": 1 }\nparticipant Q@{ type: queue, alias: Jobs }\n")
	require.Empty(t, ds)
	require.Equal(t, "boundary", model.Actors[0].Kind)
	require.Equal(t, "Public API", model.Actors[0].Label)
	require.Equal(t, []Pair{{Key: "x", Value: "1"}}, model.Actors[0].Properties)
	require.Equal(t, "queue", model.Actors[1].Kind)
	require.Equal(t, "Jobs", model.Actors[1].Label)
}

func TestExplicitAliasBeatsMetadataAliasUnlessItEqualsTheID(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nparticipant API@{ \"alias\": \"Internal\" } as External\nparticipant DB@{ \"alias\": \"Store\" } as DB\n")
	require.Empty(t, ds)
	require.Equal(t, "External", model.Actors[0].Label)
	require.Equal(t, []Pair{{Key: "alias", Value: "Internal"}}, model.Actors[0].Properties)
	require.Equal(t, "Store", model.Actors[1].Label)
}

func TestMetadataOnSeveralLinesReadsABlockMapping(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nparticipant O@{\ntype: database\nalias: Oh\n}\n")
	require.Empty(t, ds)
	require.Equal(t, "database", model.Actors[0].Kind)
	require.Equal(t, "Oh", model.Actors[0].Label)
}

func TestIndentedMetadataOnSeveralLinesIsRejectedLikeUpstream(t *testing.T) {
	for _, c := range []struct {
		src  string
		span source.Span
	}{
		{"sequenceDiagram\nparticipant A@{\n  type: database\n  alias: Disk\n}\n", source.Span{Start: 51, End: 57}},
		{"sequenceDiagram\nparticipant A@{\n  type: database\n  type: queue\n}\n", source.Span{Start: 51, End: 56}},
	} {
		model, ds := resolveSource(c.src)
		require.Len(t, ds, 1, c.src)
		require.Equal(t, "config/malformed", ds[0].Code)
		require.Equal(t, "malformed config value", ds[0].Message)
		require.Equal(t, c.span, ds[0].Span, c.src)
		require.Equal(t, "participant", model.Actors[0].Kind, "a rejected body has no model effect")
	}
}

func TestMetadataReaderDiagnosticsReachTheSourceSpans(t *testing.T) {
	for _, c := range []struct {
		src     string
		message string
		span    source.Span
	}{
		{"sequenceDiagram\nparticipant A@{ type: database, type: queue }\n", "duplicate key", source.Span{Start: 48, End: 52}},
		{"sequenceDiagram\nparticipant A@{\ntype: database\ntype: queue\n}\n", "duplicate key", source.Span{Start: 47, End: 51}},
		{"sequenceDiagram\nparticipant A@{ type: x, }\n", "malformed config value", source.Span{Start: 41, End: 42}},
		{"sequenceDiagram\nparticipant A@{ type: x,\n}\n", "malformed config value", source.Span{Start: 41, End: 42}},
		{"sequenceDiagram\nparticipant A@{ \"type: \"entity\" }\n", "malformed config value", source.Span{Start: 40, End: 49}},
	} {
		_, ds := resolveSource(c.src)
		require.Len(t, ds, 1, c.src)
		require.Equal(t, "config/malformed", ds[0].Code, c.src)
		require.Equal(t, c.message, ds[0].Message, c.src)
		require.Equal(t, c.span, ds[0].Span, c.src)
	}
}

func TestLinkWithoutAtSignKeepsTheWholeTextAsTheURL(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nlink A: foo\nlink B: @url\nlink C: éé@ u\nlink D: abc  \n")
	require.Empty(t, ds)
	require.Equal(t, []Pair{{Key: "f", Value: "foo"}}, model.Actors[0].Links)
	require.Equal(t, []Pair{{Key: "@ur", Value: "url"}}, model.Actors[1].Links)
	require.Equal(t, []Pair{{Key: "é", Value: "u"}}, model.Actors[2].Links)
	require.Equal(t, []Pair{{Key: "a", Value: "abc"}}, model.Actors[3].Links)
}

func TestRepeatedLinkLabelReplacesTheEarlierURL(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nlink A: Docs @ https://one.dev\nlink A: Wiki @ https://wiki.dev\nlink A: Docs @ https://two.dev\nlinks A: {\"Wiki\": \"https://three.dev\"}\n")
	require.Empty(t, ds)
	require.Equal(t, []Pair{{Key: "Docs", Value: "https://two.dev"}, {Key: "Wiki", Value: "https://three.dev"}}, model.Actors[0].Links)
}

func TestPropertiesAndDetailsJSONFormsMapOntoPropertiesAndLinks(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nproperties A: {\"p\": \"v\", \"q\": true, \"n\": null, \"o\": {\"x\": 1}, \"a\": [1], \"d\": 1.5}\ndetails B: {\"properties\": {\"k\": \"v\"}, \"links\": {\"L\": \"https://l.dev\"}, \"other\": 1}\ndetails B: {\"properties\": {\"k\": \"w\"}}\ndetails C: {\"k\": \"v\"}\ndetails D: element-id\nproperties E: [1]\n")
	require.Empty(t, ds)
	require.Equal(t, []Pair{{Key: "p", Value: "v"}, {Key: "q", Value: "true"}, {Key: "d", Value: "1.5"}}, model.Actors[0].Properties)
	require.Equal(t, []Pair{{Key: "k", Value: "w"}}, model.Actors[1].Properties)
	require.Equal(t, []Pair{{Key: "L", Value: "https://l.dev"}}, model.Actors[1].Links)
	require.Empty(t, model.Actors[2].Properties, "a flat details object has no properties member")
	require.Empty(t, model.Actors[3].Properties, "a details reference that is not JSON has no effect")
	require.Empty(t, model.Actors[4].Properties, "a JSON array has no effect")
}

func TestLinkStatementsDropTheColonBeforeTheirText(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nlink A: Dash @ https://x.dev\nlink B: wrap: Wrapped @ https://w.dev\nlinks C: {\"k\": \"https://k.dev\", \"n\": 2}\nproperties D: {\"p\": \"v\", \"q\": true}\nproperties D: {\"p\": \"w\"}\ndetails E: {\"properties\": {\"d\": \"v\"}}\nlinks F: not json\n")
	require.Empty(t, ds)
	require.Equal(t, []Pair{{Key: "Dash", Value: "https://x.dev"}}, model.Actors[0].Links)
	require.Equal(t, []Pair{{Key: "Wrapped", Value: "https://w.dev"}}, model.Actors[1].Links)
	require.Equal(t, []Pair{{Key: "k", Value: "https://k.dev"}, {Key: "n", Value: "2"}}, model.Actors[2].Links)
	require.Equal(t, []Pair{{Key: "p", Value: "w"}, {Key: "q", Value: "true"}}, model.Actors[3].Properties)
	require.Equal(t, []Pair{{Key: "d", Value: "v"}}, model.Actors[4].Properties)
	require.Empty(t, model.Actors[5].Links, "malformed JSON has no model effect")
}

func TestActivationAndCreationDiagnostics(t *testing.T) {
	_, ds := resolveSource("sequenceDiagram\nA->>-B: x\ndeactivate A\n")
	require.Equal(t, []string{"sequence/inactive-participant", "sequence/inactive-participant"}, codes(ds))
	_, ds = resolveSource("sequenceDiagram\nA->>B: x\ncreate participant B\nA->>B: y\n")
	require.Equal(t, []string{"sequence/create-existing-participant"}, codes(ds))
	_, ds = resolveSource("sequenceDiagram\ncreate participant C\nA->>B: x\n")
	require.Equal(t, []string{"sequence/creating-message-missing"}, codes(ds))
	_, ds = resolveSource("sequenceDiagram\nA->>B: x\ndestroy C\nA->>B: y\n")
	require.Equal(t, []string{"sequence/destroying-message-missing"}, codes(ds))
}

func TestBoxMembershipConflict(t *testing.T) {
	_, ds := resolveSource("sequenceDiagram\nbox one\nparticipant A\nend\nbox two\nparticipant A\nend\n")
	require.Equal(t, []string{"sequence/participant-box-conflict"}, codes(ds))
}

func TestAutonumberPrefixesMessagesWithTheRunningNumber(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nautonumber 5 2\nA->>B: one\nA->>B: two\nautonumber off\nA->>B: three\n")
	require.Empty(t, ds)
	var texts []string
	for _, event := range model.Events {
		if message, ok := event.(*Message); ok {
			texts = append(texts, message.Text)
		}
	}
	require.Equal(t, []string{"(5) one", "(7) two", "three"}, texts)
}

func TestSequenceConfigHonoursKnownKeysOnly(t *testing.T) {
	model, ds := resolveSource("---\nconfig:\n  sequence:\n    wrap: true\n    actorMargin: 80\n    mirrorActors: false\n---\nsequenceDiagram\nA->>B: x\n")
	require.Empty(t, ds)
	require.True(t, model.Wrap)
	require.Equal(t, []ConfigEntry{{Key: "actorMargin", Value: DumpValue{Kind: DumpInteger, Integer: 80}}, {Key: "wrap", Value: DumpValue{Kind: DumpBool, Bool: true}}}, model.Config)
}

func TestNotePlacementFoldsAsciiCaseOfKeyword(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nNote RIGHT OF A: x\nnote right of A: y\nnote over A,B: z\nNOTE Left Of A: w\nNote OVER A: v\n")
	require.Empty(t, ds)
	var placements []Placement
	for _, event := range model.Events {
		if note, ok := event.(*Note); ok {
			placements = append(placements, note.Placement)
		}
	}
	require.Equal(t, []Placement{RightOf, RightOf, Over, LeftOf, Over}, placements)
}

func TestFragmentEventsNestInSourceOrder(t *testing.T) {
	model, ds := resolveSource("sequenceDiagram\nalt a\nA->>B: x\nelse b\nloop c\nA->>B: y\nend\nend\n")
	require.Empty(t, ds)
	var shape []string
	for _, event := range model.Events {
		switch event.(type) {
		case *FragmentStart:
			shape = append(shape, "start")
		case *FragmentElse:
			shape = append(shape, "else")
		case *FragmentEnd:
			shape = append(shape, "end")
		case *Message:
			shape = append(shape, "message")
		}
	}
	require.Equal(t, []string{"start", "message", "else", "start", "message", "end", "end"}, shape)
}
