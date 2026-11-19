package syntax_test

import (
	"reflect"
	"strconv"
	"strings"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/diag"
	"github.com/gosuda/elegant-mermaid/internal/source"
	"github.com/gosuda/elegant-mermaid/internal/syntax/agentflow"
	"github.com/gosuda/elegant-mermaid/internal/syntax/c4"
	"github.com/gosuda/elegant-mermaid/internal/syntax/class"
	"github.com/gosuda/elegant-mermaid/internal/syntax/er"
	"github.com/gosuda/elegant-mermaid/internal/syntax/flowchart"
	"github.com/gosuda/elegant-mermaid/internal/syntax/requirement"
	"github.com/gosuda/elegant-mermaid/internal/syntax/sequence"
	"github.com/gosuda/elegant-mermaid/internal/syntax/state"
	"github.com/gosuda/elegant-mermaid/internal/syntax/swimlane"
	"github.com/gosuda/elegant-mermaid/internal/syntax/usecase"
)

const commentLine = "%% c\n"

type parseFunc func(src []byte, removed []source.Span) (any, []diag.Diagnostic)

func adapt[T any](f func([]byte, []source.Span) (*T, []diag.Diagnostic)) parseFunc {
	return func(src []byte, removed []source.Span) (any, []diag.Diagnostic) {
		tree, diags := f(src, removed)
		return tree, diags
	}
}

func fingerprint(v reflect.Value, out *[]string) {
	switch v.Kind() {
	case reflect.Pointer, reflect.Interface:
		if v.IsNil() {
			*out = append(*out, "nil")
			return
		}
		fingerprint(v.Elem(), out)
	case reflect.Struct:
		if v.Type() == reflect.TypeOf(source.Span{}) {
			return
		}
		for i := range v.NumField() {
			fingerprint(v.Field(i), out)
		}
	case reflect.Slice, reflect.Array:
		*out = append(*out, "["+strconv.Itoa(v.Len()))
		for i := range v.Len() {
			fingerprint(v.Index(i), out)
		}
	case reflect.String:
		*out = append(*out, strconv.Quote(v.String()))
	case reflect.Bool:
		*out = append(*out, strconv.FormatBool(v.Bool()))
	default:
	}
}

func describe(parse parseFunc, src string, removed []source.Span) []string {
	tree, diags := parse([]byte(src), removed)
	var out []string
	fingerprint(reflect.ValueOf(tree), &out)
	for _, d := range diags {
		out = append(out, "diag "+d.Code+" "+strconv.Quote(d.Message))
	}
	return out
}

func TestCommentLineIsInvisibleInsideMultilineTokens(t *testing.T) {
	const accessibility = "accDescr {\nfirst\n" + commentLine + "second\n}\n"
	kinds := []struct {
		name    string
		parse   parseFunc
		sources []string
	}{
		{"flowchart", adapt(flowchart.Parse), []string{
			"flowchart TD\n" + accessibility + "A-->B\n",
			"flowchart TD\nA[\"one\n" + commentLine + "two\"]-->B\n",
			"flowchart TD\nclick\n" + commentLine + " A callback\n",
		}},
		{"swimlane", adapt(swimlane.Parse), []string{
			"swimlane-beta TD\n" + accessibility + "A-->B\n",
			"swimlane-beta TD\nA --> B\n" + commentLine + "  --> C\n",
		}},
		{"agentflow", adapt(agentflow.Parse), []string{
			"agentflow-beta\n" + accessibility + "A-->B\n",
			"agentflow-beta\nA[\"one\n" + commentLine + "two\"]-->B\n",
			"agentflow-beta\nA@{ label: x,\n" + commentLine + " shape: task }\n",
		}},
		{"class", adapt(class.Parse), []string{
			"classDiagram\n" + accessibility + "class A\n",
			"classDiagram\nclass A[\"one\n" + commentLine + "two\"]\n",
		}},
		{"state", adapt(state.Parse), []string{
			"stateDiagram-v2\n" + accessibility + "A --> B\n",
			"stateDiagram-v2\nstate \"one\n" + commentLine + "two\" as A\n",
			"stateDiagram-v2\nnote left of A\nfirst\n" + commentLine + "second\nend note\n",
		}},
		{"er", adapt(er.Parse), []string{
			"erDiagram\n" + accessibility + "A ||--|| B : r\n",
			"erDiagram\nA {\n`one\n" + commentLine + "two` int\n}\n",
		}},
		{"requirement", adapt(requirement.Parse), []string{
			"requirementDiagram\n" + accessibility + "requirement r {\nid: 1\n}\n",
			"requirementDiagram\nrequirement r {\nid: 1\ntext: \"one\n" + commentLine + "two\"\n}\n",
		}},
		{"usecase", adapt(usecase.Parse), []string{
			"usecase-beta\n" + accessibility + "actor A\n",
			"usecase-beta\nA(\"`one\n" + commentLine + "two`\")\n",
		}},
		{"c4", adapt(c4.Parse), []string{
			"C4Context\n" + accessibility + "Person(a,\"A\")\n",
			"C4Context\nPerson(a,\"one\n" + commentLine + "two\")\n",
		}},
		{"sequence", adapt(sequence.Parse), []string{
			"sequenceDiagram\n" + accessibility + "A->>B: x\n",
			"sequenceDiagram\nparticipant A@{ \"type\": \"actor\",\n" + commentLine + " \"x\": 1 }\n",
		}},
	}
	for _, kind := range kinds {
		t.Run(kind.name, func(t *testing.T) {
			for _, with := range kind.sources {
				before, after, found := strings.Cut(with, commentLine)
				if !found {
					t.Fatalf("source has no comment line: %q", with)
				}
				removed := []source.Span{{Start: len(before), End: len(before) + len(commentLine)}}
				without := before + after
				got := describe(kind.parse, with, removed)
				want := describe(kind.parse, without, nil)
				if strings.Join(got, "\n") != strings.Join(want, "\n") {
					t.Errorf("comment line changes the parse of %q\nwith comment:\n  %s\nwithout comment:\n  %s",
						with, strings.Join(got, "\n  "), strings.Join(want, "\n  "))
				}
			}
		})
	}
}
