package termgfx

import (
	"bytes"
	"strconv"
	"strings"
)

const (
	kittyQuery   = "\x1b_Gi=31,s=1,v=1,a=q,t=d,f=24;AAAA\x1b\\"
	cellSizeQry  = "\x1b[16t"
	da1Query     = "\x1b[c"
	kittyOKToken = "i=31;OK"
)

func QueryBytes(env Env) []byte {
	out := make([]byte, 0, len(kittyQuery)+len(cellSizeQry)+len(da1Query))
	if env.KittyCandidate() {
		out = append(out, kittyQuery...)
	}
	out = append(out, cellSizeQry...)
	return append(out, da1Query...)
}

func ParseReplies(stream []byte) Replies {
	replies := Replies{CellW: FallbackCellW, CellH: FallbackCellH}
	for index := 0; index < len(stream); {
		consumed, stop := parseReply(stream[index:], &replies)
		index += consumed
		if stop {
			break
		}
	}
	return replies
}

func AutoMode(env Env, replies Replies) Mode {
	switch {
	case replies.KittyOK:
		return ModeKitty
	case env.TermProgram == "iTerm.app":
		return ModeITerm2
	case replies.Sixel:
		return ModeSixel
	}
	return ModeCells
}

func parseReply(stream []byte, replies *Replies) (int, bool) {
	if len(stream) < 2 || stream[0] != escByte {
		return 1, false
	}
	switch stream[1] {
	case '_':
		return parseAPC(stream, replies), false
	case '[':
		return parseCSI(stream, replies)
	}
	return 1, false
}

func parseAPC(stream []byte, replies *Replies) int {
	body, rest, found := bytes.Cut(stream[2:], []byte(stSeq))
	if !found {
		return len(stream)
	}
	if bytes.Contains(body, []byte(kittyOKToken)) {
		replies.KittyOK = true
	}
	return len(stream) - len(rest)
}

func parseCSI(stream []byte, replies *Replies) (int, bool) {
	params, final, consumed, complete := scanCSI(stream)
	if !complete {
		return consumed, false
	}
	switch final {
	case 't':
		applyCellSize(params, replies)
	case 'c':
		return consumed, applyDA1(params, replies)
	}
	return consumed, false
}

func scanCSI(stream []byte) (string, byte, int, bool) {
	for index := 2; index < len(stream); index++ {
		c := stream[index]
		if c >= 0x40 && c <= 0x7e {
			return string(stream[2:index]), c, index + 1, true
		}
		if c < 0x20 || c > 0x3f {
			return "", 0, index + 1, false
		}
	}
	return "", 0, len(stream), false
}

func applyCellSize(params string, replies *Replies) {
	rest, ok := strings.CutPrefix(params, "6;")
	if !ok {
		return
	}
	heightText, widthText, ok := strings.Cut(rest, ";")
	if !ok || strings.Contains(widthText, ";") {
		return
	}
	height, errH := strconv.ParseUint(heightText, 10, strconv.IntSize-1)
	width, errW := strconv.ParseUint(widthText, 10, strconv.IntSize-1)
	if errH != nil || errW != nil || height == 0 || width == 0 {
		return
	}
	replies.CellH = int(height)
	replies.CellW = int(width)
}

func applyDA1(params string, replies *Replies) bool {
	rest, ok := strings.CutPrefix(params, "?")
	if !ok {
		return false
	}
	sixel := false
	for field := range strings.SplitSeq(rest, ";") {
		value, err := strconv.ParseUint(field, 10, 32)
		if err != nil {
			return false
		}
		if value == 4 {
			sixel = true
		}
	}
	replies.Sixel = sixel
	return true
}
