package lanes

import (
	"errors"

	"github.com/gosuda/elegant-mermaid/internal/geom"
	"github.com/gosuda/elegant-mermaid/internal/scene"
)

const NoBand = -1

var ErrJourneyInput = errors.New("journey layout: malformed input")

type JourneyTitle struct {
	ID    string
	Label Text
}

type JourneySection struct {
	ID    string
	Label Text
}

type JourneyTask struct {
	ID     string
	Band   int
	Score  int
	Label  Text
	People *Text
}

type JourneyInput struct {
	Title                                        *JourneyTitle
	Sections                                     []JourneySection
	Tasks                                        []JourneyTask
	TaskWidth, TaskHeight, BandHeight, ColumnGap int64
}

type JourneyResult struct {
	Canvas geom.Size
	Title  geom.Rect
	Frames []geom.Rect
	Bands  []geom.Rect
	Tasks  []geom.Rect
	People []geom.Rect
	Faces  []geom.Point
	Groups []*scene.Group
}

type journeyPlanner struct {
	in       JourneyInput
	c        journeyConstants
	profile  scene.Profile
	first    []int
	last     []int
	bandH    int64
	taskH    int64
	bandTop  int64
	title    box
	frames   []box
	bands    []box
	tasks    []box
	faces    []vec
	sections []box
	names    []box
	people   []box
}

func Journey(in JourneyInput, p Params) (JourneyResult, error) {
	c, err := loadJourneyConstants(p.Profile, in)
	if err != nil {
		return JourneyResult{}, err
	}
	pl := &journeyPlanner{in: in, c: c, profile: p.Profile}
	if err := pl.group(); err != nil {
		return JourneyResult{}, err
	}
	pl.size()
	pl.place()
	return pl.result()
}

func (pl *journeyPlanner) group() error {
	pl.first = make([]int, len(pl.in.Sections))
	pl.last = make([]int, len(pl.in.Sections))
	for i := range pl.first {
		pl.first[i], pl.last[i] = -1, -1
	}
	for k, t := range pl.in.Tasks {
		if !pl.validTask(t) {
			return ErrJourneyInput
		}
		if t.Band == NoBand {
			continue
		}
		if pl.first[t.Band] < 0 {
			pl.first[t.Band] = k
		}
		pl.last[t.Band] = k
	}
	for b := range pl.in.Sections {
		if pl.first[b] < 0 || !pl.consecutive(b) {
			return ErrJourneyInput
		}
	}
	return nil
}

func (pl *journeyPlanner) validTask(t JourneyTask) bool {
	return t.Band >= NoBand && t.Band < len(pl.in.Sections) && int64(t.Score) >= pl.c.scoreMin && int64(t.Score) <= pl.c.scoreMax
}

func (pl *journeyPlanner) consecutive(band int) bool {
	for k := pl.first[band]; k <= pl.last[band]; k++ {
		if pl.in.Tasks[k].Band != band {
			return false
		}
	}
	return true
}

func (pl *journeyPlanner) size() {
	pl.bandH, pl.taskH = pl.c.bandHeight, pl.c.taskHeight
	for _, s := range pl.in.Sections {
		pl.bandH = max(pl.bandH, int64(s.Label.H)+2*pl.c.padY)
	}
	for _, t := range pl.in.Tasks {
		pl.taskH = max(pl.taskH, pl.textHeight(t)+2*pl.c.padY)
	}
}

func (pl *journeyPlanner) textHeight(t JourneyTask) int64 {
	h := int64(t.Label.H)
	if t.People != nil {
		h += int64(t.People.H)
	}
	return h
}

func (pl *journeyPlanner) pitch() int64 { return pl.c.taskWidth + pl.c.columnGap }

func (pl *journeyPlanner) column(k int) int64 { return int64(k) * pl.pitch() }

func (pl *journeyPlanner) faceY(score int) int64 {
	return pl.bandTop + pl.bandH + (pl.c.scoreMax-int64(score))*pl.c.scoreStep + pl.c.scoreStep
}

func (pl *journeyPlanner) place() {
	if t := pl.in.Title; t != nil {
		pl.title = box{w: int64(t.Label.W), h: int64(t.Label.H)}
		pl.bandTop = pl.title.h + pl.c.scoreStep
	}
	bandBottom := pl.bandTop + pl.bandH
	taskTop := bandBottom + (pl.c.scoreMax-pl.c.scoreMin+2)*pl.c.scoreStep
	for b, s := range pl.in.Sections {
		x := pl.column(pl.first[b])
		w := int64(pl.last[b]-pl.first[b])*pl.pitch() + pl.c.taskWidth
		pl.frames = append(pl.frames, box{x: x, y: pl.bandTop, w: w, h: taskTop + pl.taskH - pl.bandTop})
		pl.bands = append(pl.bands, box{x: x, y: pl.bandTop, w: w, h: pl.bandH})
		pl.sections = append(pl.sections, pl.centred(box{x: x, y: pl.bandTop, w: w, h: pl.bandH}, int64(s.Label.H)))
	}
	for k, t := range pl.in.Tasks {
		card := box{x: pl.column(k), y: taskTop, w: pl.c.taskWidth, h: pl.taskH}
		pl.tasks = append(pl.tasks, card)
		pl.faces = append(pl.faces, vec{x: card.x + half(card.w), y: pl.faceY(t.Score)})
		pl.placeText(card, t)
	}
}

func (pl *journeyPlanner) centred(card box, height int64) box {
	return box{x: card.x + pl.c.padX, y: card.y + half(card.h-height), w: card.w - 2*pl.c.padX, h: height}
}

func (pl *journeyPlanner) placeText(card box, t JourneyTask) {
	block := pl.centred(card, pl.textHeight(t))
	name := box{x: block.x, y: block.y, w: block.w, h: int64(t.Label.H)}
	pl.names = append(pl.names, name)
	if t.People == nil {
		pl.people = append(pl.people, box{})
		return
	}
	pl.people = append(pl.people, box{x: block.x, y: name.bottom(), w: block.w, h: int64(t.People.H)})
}
