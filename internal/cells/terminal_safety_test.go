package cells

import (
	"fmt"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/measure"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

func terminalControlRunes() []rune {
	var controls []rune
	for r := rune(0); r <= 0x9F; r++ {
		if r < 0x20 || r >= 0x7F {
			controls = append(controls, r)
		}
	}
	return controls
}

func TestTerminalLabelControls(t *testing.T) {
	for _, r := range terminalControlRunes() {
		t.Run(fmt.Sprintf("U+%04X", r), func(t *testing.T) {
			assertTerminalLabelControl(t, r)
		})
	}
}

func assertTerminalLabelControl(t *testing.T, r rune) {
	t.Helper()
	c, err := New(3, 1)
	if err != nil {
		t.Fatal(err)
	}
	p := &scene.Text{Rect: geom.Rect{W: 3, H: 1}}
	n, err := c.placeLine(p, "a"+string(r)+"b", 0, TokenFG)
	if err != nil || n != 0 {
		t.Fatalf("placement: refused=%d err=%v", n, err)
	}
	if got := string(c.Serialise(CharsetUnicode, ColorNone, nil)); got != "a�b\n" {
		t.Fatalf("bytes: %q", got)
	}
	if w := measure.ClusterWidth(measure.Cluster{Text: string(r)}); w != 1 {
		t.Fatalf("control width: %d", w)
	}
}

type terminalColourCase struct {
	mode ColorMode
	sgr  string
}

func TestTerminalCanvasFieldsAllColours(t *testing.T) {
	modes := []terminalColourCase{
		{ColorNone, ""},
		{ColorANSI16, "\x1b[30m"},
		{ColorANSI256, "\x1b[38;5;16m"},
		{ColorTruecolor, "\x1b[38;2;0;0;0m"},
	}
	for _, mode := range modes {
		for _, r := range terminalControlRunes() {
			assertTerminalCanvasControl(t, mode, r)
		}
	}
}

func assertTerminalCanvasControl(t *testing.T, mode terminalColourCase, r rune) {
	t.Helper()
	c, err := New(5, 1)
	if err != nil {
		t.Fatal(err)
	}
	c.Put(0, 0, func(v *Cell) { v.Label = string(r); v.LabelInk = TokenBorder })
	c.Put(1, 0, func(v *Cell) { v.Symbol = r; v.Ink = TokenBorder })
	if !c.PutLabel(2, 0, "é", 1, TokenBorder) || !c.PutLabel(3, 0, "界", 2, TokenBorder) {
		t.Fatal("normal Unicode label refused")
	}
	symbol := "�"
	if r == 0 {
		symbol = " "
	}
	want := mode.sgr + "�" + symbol + "é界"
	if mode.mode != ColorNone {
		want += "\x1b[39m"
	}
	want += "\n"
	got := c.Serialise(CharsetUnicode, mode.mode, func(Token) RGB { return RGB{} })
	if string(got) != want {
		t.Fatalf("mode %d scalar U+%04X: got %q want %q", mode.mode, r, got, want)
	}
}
