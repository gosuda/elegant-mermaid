package tui

import (
	"image"

	"github.com/gosuda/elegant-mermaid/internal/termgfx"
)

type Scheduler struct {
	Latest, Inflight, Displayed uint64
	Cancelled                   bool
}

func (s *Scheduler) Edit() bool {
	s.Latest++
	if s.Inflight == 0 {
		s.Inflight = s.Latest
		return true
	}
	s.Cancelled = true
	return false
}

func (s *Scheduler) Done() bool {
	if s.Cancelled {
		s.Inflight = s.Latest
		s.Cancelled = false
		return false
	}
	s.Displayed = s.Inflight
	s.Inflight = 0
	return true
}

type State struct {
	Path, Kind, Theme                       string
	Width, Height, Block, Blocks            int
	Mode                                    termgfx.Mode
	Fit, ASCII, Empty, WatchLost, AutoPanel bool
	Zoom, Errors, Warnings                  int
	Displayed, FrameRev                     uint64
	Panel                                   string
	Diagnostics, Text                       []string
	MissingBlocks                           bool
	ColoredText                             []string
	Color                                   int
	ContentW, ContentH, OffsetX, OffsetY    int
	Pixels                                  *image.RGBA
	CellW, CellH                            int
}

func New(path, theme string) State {
	return State{Path: path, Theme: theme, Width: 80, Height: 24, Zoom: 100, Fit: true, CellW: 8, CellH: 16}
}

func (s *State) Extent() (int, int, int, int) {
	if s.Mode.Pixel() && s.Pixels != nil {
		return (s.Pixels.Bounds().Dx()*s.Zoom + 99) / 100, (s.Pixels.Bounds().Dy()*s.Zoom + 99) / 100, s.Width * s.CellW, (s.Height - 2) * s.CellH
	}
	return s.ContentW, s.ContentH, s.Width, s.Height - 2
}

func (s *State) Clamp() {
	w, h, vw, vh := s.Extent()
	s.OffsetX = max(0, min(s.OffsetX, w-vw))
	s.OffsetY = max(0, min(s.OffsetY, h-vh))
}

func (s *State) FitImage() {
	if s.Fit && s.Mode.Pixel() && s.Pixels != nil {
		s.Zoom = max(10, min(800, min(s.Width*s.CellW*100/s.Pixels.Bounds().Dx(), (s.Height-2)*s.CellH*100/s.Pixels.Bounds().Dy())))
	}
	s.Clamp()
}

func (s *State) Resize(w, h int) {
	_, _, oldW, oldH := s.Extent()
	s.Width = max(20, w)
	s.Height = max(5, h)
	_, _, newW, newH := s.Extent()
	s.OffsetX += oldW/2 - newW/2
	s.OffsetY += oldH/2 - newH/2
	s.FitImage()
}

func (s *State) Key(key string) (bool, bool) {
	if key == "q" || key == "ctrl-c" {
		return false, true
	}
	if s.panKey(key) || s.zoomKey(key) || s.panelKey(key) {
		s.Clamp()
		return false, false
	}
	edit := s.editKey(key)
	s.Clamp()
	return edit, false
}

func (s *State) panKey(key string) bool {
	dx, dy := 1, 1
	if s.Mode.Pixel() {
		dx = s.CellW
		dy = s.CellH
	}
	switch key {
	case "left", "h":
		s.OffsetX -= dx
	case "right", "l":
		s.OffsetX += dx
	case "up", "k":
		s.OffsetY -= dy
	case "down", "j":
		s.OffsetY += dy
	default:
		return false
	}
	return true
}

func (s *State) zoomKey(key string) bool {
	if key == "0" {
		if s.Mode.Pixel() {
			s.Fit = true
			s.FitImage()
		} else {
			s.OffsetX = 0
			s.OffsetY = 0
		}
		return true
	}
	if key != "+" && key != "-" {
		return false
	}
	if !s.Mode.Pixel() {
		return true
	}
	s.Fit = false
	if key == "+" {
		s.Zoom = min(800, s.Zoom*5/4)
	} else {
		s.Zoom = max(10, s.Zoom*4/5)
	}
	return true
}

func (s *State) panelKey(key string) bool {
	panel := ""
	switch key {
	case "d":
		panel = "diagnostics"
	case "?":
		panel = "keys"
	case "esc":
	default:
		return false
	}
	if s.Panel == panel {
		panel = ""
	}
	s.Panel = panel
	s.AutoPanel = false
	return true
}

func (s *State) editKey(key string) bool {
	switch key {
	case "n", "p":
		return s.blockKey(key)
	case "t":
		s.nextTheme()
	case "c":
		s.ASCII = !s.ASCII
	case "g":
		s.Mode = (s.Mode + 1) % 4
		s.Fit = true
	case "r":
	default:
		return false
	}
	return true
}

func (s *State) blockKey(key string) bool {
	if s.Blocks == 0 {
		return false
	}
	delta := 1
	if key == "p" {
		delta = -1
	}
	s.Block = (s.Block-1+delta+s.Blocks)%s.Blocks + 1
	return true
}

func (s *State) nextTheme() {
	themes := [...]string{"elegant-light", "elegant-dark", "github-light", "github-dark", "catppuccin-latte", "catppuccin-mocha", "nord", "solarized-light", "solarized-dark"}
	next := 0
	for i, theme := range themes {
		if theme == s.Theme {
			next = (i + 1) % len(themes)
		}
	}
	s.Theme = themes[next]
}
