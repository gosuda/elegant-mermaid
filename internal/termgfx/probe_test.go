package termgfx_test

import (
	"strconv"
	"testing"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
)

func TestParseRepliesCellGrammar(t *testing.T) {
	maxInt := int(^uint(0) >> 1)
	for _, value := range []string{"+32;12", "32;+12", "-16;8", "16;0", ";8", "16;8;1", "16; 8", "16;0x8", "16;" + strconv.FormatUint(uint64(maxInt)+1, 10)} {
		t.Run(value, func(t *testing.T) {
			got := termgfx.ParseReplies([]byte("\x1b[6;" + value + "t"))
			if got.CellW != 8 || got.CellH != 16 {
				t.Fatalf("malformed cell reply %q changed fallback: %+v", value, got)
			}
		})
	}
	got := termgfx.ParseReplies([]byte("noise\x1b[6;032;012t\x1b[?1;4c\x1b[6;99;99t"))
	if got.CellW != 12 || got.CellH != 32 || !got.Sixel {
		t.Fatalf("decimal cell size before DA1 must win, late reply ignored: %+v", got)
	}
	got = termgfx.ParseReplies([]byte("\x1b[6;" + strconv.Itoa(maxInt) + ";1t"))
	if got.CellH != maxInt || got.CellW != 1 {
		t.Fatalf("positive int boundary rejected: %+v", got)
	}
}

func TestParseRepliesDA1Grammar(t *testing.T) {
	for _, params := range []string{"?", "?4;", "?;4", "?4;;1", "?4:1", "?4+1", "?4;4294967296", "4"} {
		got := termgfx.ParseReplies([]byte("\x1b[" + params + "c\x1b[6;24;10t"))
		if got.Sixel || got.CellW != 10 || got.CellH != 24 {
			t.Errorf("invalid DA1 %q must not claim support or end probe: %+v", params, got)
		}
	}
}

func TestParseRepliesDA1NumericStop(t *testing.T) {
	leadingZero := termgfx.ParseReplies([]byte("\x1b[?1;04c\x1b[6;24;10t"))
	if !leadingZero.Sixel || leadingZero.CellW != 8 || leadingZero.CellH != 16 {
		t.Fatalf("numeric DA1 parameter 04 must enable Sixel and end probe: %+v", leadingZero)
	}
}

func TestParseRepliesCapabilityPriority(t *testing.T) {
	got := termgfx.ParseReplies([]byte("\x1b_Gi=31;OK\x1b\\\x1b[?1;4c\x1b[6;24;10t"))
	if !got.KittyOK || !got.Sixel || got.CellW != 8 {
		t.Fatalf("replies before DA1 must count and replies after it must not: %+v", got)
	}
	if termgfx.AutoMode(termgfx.Env{TermProgram: "iTerm.app"}, got) != termgfx.ModeKitty {
		t.Fatal("Kitty acknowledgement must outrank iTerm environment and Sixel")
	}
}
