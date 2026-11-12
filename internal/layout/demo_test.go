package layout

import "testing"

const demoSource = "flowchart LR\n  A[Start] --> B{Choice}\n  B -->|yes| C[Done]\n  B -->|no| A\n"

const demoDump = `{"version":1,"stage":"model","kind":"flowchart","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"LR","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},
"boxes":[{"id":"A","role":"node","parent":"","exclusive":true},
{"id":"B","role":"node","parent":"","exclusive":true},
{"id":"C","role":"node","parent":"","exclusive":true}],
"routes":[{"id":"e0","from":"A","to":"B","orthogonal":true},
{"id":"e1","from":"B","to":"C","orthogonal":true},
{"id":"e2","from":"B","to":"A","orthogonal":true}],
"labels":[{"id":"A.label","owner":"A","text":"Start","lines":[]},
{"id":"B.label","owner":"B","text":"Choice","lines":[]},
{"id":"C.label","owner":"C","text":"Done","lines":[]},
{"id":"e1.label","owner":"e1","text":"yes","lines":[]},
{"id":"e2.label","owner":"e2","text":"no","lines":[]}]}
`

func TestDemoModelDump(t *testing.T) {
	in, ok := inputSource(t, []byte(demoSource))
	if !ok {
		t.Fatal("demo rejected")
	}
	if got := string(dumpInput(t, in)); got != demoDump {
		t.Fatalf("got %s", got)
	}
}
