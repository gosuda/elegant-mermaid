package layered

import (
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func TestPipelineLowersMeasuredMath(t *testing.T) {
	cases := []struct {
		name, source string
		profile      scene.Profile
		want         []string
	}{
		{"mixed", "From $$x(t)$$ to $$y(t)$$", scene.ProfileVector, []string{"From ", "x", "(", "t", ")", " to ", "y", "(", "t", ")"}},
		{"unsupported", `From $$\tilde{x}$$`, scene.ProfileVector, []string{`From $$\tilde{x}$$`}},
		{"cells", "From $$x(t)$$", scene.ProfileCell, []string{"From $$x(t)$$"}},
	}
	for _, test := range cases {
		t.Run(test.name, func(t *testing.T) {
			in := Input{Kind: "flowchart", Boxes: []scene.Box{{ID: "A", Role: scene.RoleNode, Exclusive: true}}, Text: []string{test.source}}
			o := scene.DefaultOptions()
			o.Profile = test.profile
			s, err := LayoutFamily(in, Options{Scene: o})
			if err != nil {
				t.Fatal(err)
			}
			got := mathSceneTexts(s)
			if len(got) != len(test.want) {
				t.Fatalf("text primitives = %q, want %q", got, test.want)
			}
			for i := range got {
				if got[i] != test.want[i] {
					t.Fatalf("text primitives = %q, want %q", got, test.want)
				}
			}
		})
	}
}

func mathSceneTexts(s scene.Scene) []string {
	var texts []string
	for _, group := range s.Groups {
		for _, item := range group.Items {
			text, ok := item.(*scene.Text)
			if ok {
				texts = append(texts, mathTextContent(text))
			}
		}
	}
	return texts
}

func mathTextContent(text *scene.Text) string {
	value := ""
	for _, line := range text.Lines {
		for _, run := range line {
			value += run.Text
		}
	}
	return value
}
