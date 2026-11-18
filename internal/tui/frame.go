package tui

import (
	"fmt"
	"strings"
	"unicode"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
)

const (
	keyRow       = "? help  q quit  d diagnostics  arrows/hjkl pan  0 fit"
	emptyMessage = "Empty diagram: add a Mermaid header such as flowchart TD; waiting for changes"
)

func pad(text string, width int) string {
	clean := strings.Map(func(r rune) rune {
		if unicode.IsControl(r) {
			return '�'
		}
		return r
	}, text)
	runes := []rune(clean)
	runes = runes[:min(len(runes), width)]
	return string(runes) + strings.Repeat(" ", width-len(runes))
}

func Frame(s State) string {
	rows := viewport(s)
	rows = append(rows, status(s), keyRow)
	for i := range rows {
		rows[i] = pad(rows[i], s.Width)
	}
	return strings.Join(rows, "\n") + "\n"
}

func viewport(s State) []string {
	if s.Panel != "" {
		return panel(s)
	}
	if s.MissingBlocks {
		return wrapMessage("no Mermaid blocks found in "+s.Path+"; add a fenced code block labelled mermaid", s.Width, s.Height-2)
	}
	if s.Empty {
		return wrapMessage(emptyMessage, s.Width, s.Height-2)
	}
	rows := make([]string, s.Height-2)
	if s.Mode != termgfx.ModeCells || s.FrameRev == 0 {
		return rows
	}
	for r := range rows {
		index := s.OffsetY + r
		if index >= len(s.Text) {
			continue
		}
		line := []rune(s.Text[index])
		rows[r] = string(line[min(s.OffsetX, len(line)):])
	}
	return rows
}

func wrapMessage(text string, width, height int) []string {
	rows := make([]string, height)
	row := 0
	for word := range strings.FieldsSeq(text) {
		if row >= height {
			break
		}
		if rows[row] != "" && len([]rune(rows[row]))+1+len([]rune(word)) > width {
			row++
		}
		if row >= height {
			break
		}
		if rows[row] != "" {
			rows[row] += " "
		}
		runes := []rune(word)
		for len(runes) > width && row < height {
			rows[row] += string(runes[:width])
			runes = runes[width:]
			row++
		}
		if row < height {
			rows[row] += string(runes)
		}
	}
	return rows
}

func panel(s State) []string {
	title, content := panelContent(s)
	rows := make([]string, s.Height-2)
	rows[0] = "+- " + title + " " + strings.Repeat("-", s.Width-len(title)-5) + "+"
	slots := len(rows) - 2
	for i := range slots {
		text := ""
		if i < len(content) {
			text = content[i]
		}
		if i == slots-1 && len(content) > slots {
			text = fmt.Sprintf("... %d more", len(content)-slots+1)
		}
		rows[i+1] = "| " + pad(text, s.Width-4) + " |"
	}
	rows[len(rows)-1] = "+" + strings.Repeat("-", s.Width-2) + "+"
	return rows
}

func panelContent(s State) (string, []string) {
	if s.Panel == "keys" {
		return "Keys", []string{
			"arrows, hjkl    pan", "+ -             zoom (pixel modes)", "0               fit / origin",
			"n, p            next, previous block", "t               cycle theme", "c               toggle charset",
			"g               cycle graphics mode", "d               diagnostics panel", "r               reload INPUT",
			"?               this key reference", "Esc             close panel", "q, Ctrl-C       quit",
		}
	}
	if len(s.Diagnostics) == 0 {
		return "Diagnostics", []string{"No diagnostics"}
	}
	return "Diagnostics", s.Diagnostics
}

func status(s State) string {
	parts := statusMessages(s)
	kind := s.Kind
	if s.Displayed == 0 || s.Empty {
		kind = "-"
	}
	if s.Blocks > 0 {
		kind += fmt.Sprintf(" %d/%d", s.Block, s.Blocks)
	}
	zoom := "-"
	if s.Mode.Pixel() {
		zoom = fmt.Sprintf("%d%%", s.Zoom)
		if s.Fit {
			zoom = "fit"
		}
	}
	revision := "-"
	if s.Displayed != 0 {
		revision = fmt.Sprint(s.Displayed)
	}
	parts = append(parts, kind, s.Mode.String(), zoom, fmt.Sprintf("E %d errors W %d warnings", s.Errors, s.Warnings), "REV "+revision)
	tail := " | " + strings.Join(parts, " | ")
	path := s.Path
	if len([]rune(path+tail)) > s.Width {
		path = shortPath(path, s.Width-len([]rune(tail))-3)
	}
	return path + tail
}

func shortPath(path string, keep int) string {
	if keep < 1 {
		return "..."
	}
	runes := []rune(path)
	return "..." + string(runes[max(0, len(runes)-keep):])
}

func statusMessages(s State) []string {
	var parts []string
	if s.WatchLost {
		parts = append(parts, "WATCH LOST: recreate "+s.Path+"; retrying")
	}
	if s.Displayed != 0 && s.Errors > 0 {
		parts = append(parts, staleMessage(s))
	}
	w, h, vw, vh := s.Extent()
	if w <= vw && h <= vh {
		return parts
	}
	if s.Mode.Pixel() {
		w = (w + s.CellW - 1) / s.CellW
		h = (h + s.CellH - 1) / s.CellH
	}
	return append(parts, fmt.Sprintf("%dx%d cells; pan available", w, h))
}

func staleMessage(s State) string {
	if s.FrameRev == 0 {
		return "No valid revision yet; fix the source or press r"
	}
	return fmt.Sprintf("STALE revision %d; latest revision %d has errors", s.FrameRev, s.Displayed)
}
