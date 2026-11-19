package tui

type Scheduler struct {
	Latest, Inflight, Displayed uint64
	Cancelled                   bool
}

type Event uint8

const (
	EventEdited Event = iota
	EventRenderDone
	EventRenderAborted
)

type CommandKind uint8

const (
	CommandNone CommandKind = iota
	CommandStartRender
	CommandCancelRender
	CommandDisplay
)

type Command struct {
	Kind     CommandKind
	Revision uint64
}

func (s Scheduler) enabled(e Event) bool {
	switch e {
	case EventEdited:
		return true
	case EventRenderDone:
		return s.Inflight != 0
	case EventRenderAborted:
		return s.Inflight != 0 && s.Cancelled
	}
	return false
}

func Step(s Scheduler, e Event) (Scheduler, Command) {
	if !s.enabled(e) {
		return s, Command{}
	}
	switch e {
	case EventEdited:
		return edited(s)
	case EventRenderDone:
		return renderDone(s)
	case EventRenderAborted:
		return renderAborted(s)
	}
	return s, Command{}
}

func edited(s Scheduler) (Scheduler, Command) {
	next := s
	next.Latest++
	if s.Inflight == 0 {
		next.Inflight = next.Latest
		next.Cancelled = false
		return next, Command{Kind: CommandStartRender, Revision: next.Latest}
	}
	if s.Cancelled {
		return next, Command{}
	}
	next.Cancelled = true
	return next, Command{Kind: CommandCancelRender, Revision: s.Inflight}
}

func renderDone(s Scheduler) (Scheduler, Command) {
	next := s
	if s.Cancelled {
		next.Inflight = s.Latest
		next.Cancelled = false
		return next, Command{Kind: CommandStartRender, Revision: next.Latest}
	}
	next.Displayed = s.Inflight
	next.Inflight = 0
	return next, Command{Kind: CommandDisplay, Revision: next.Displayed}
}

func renderAborted(s Scheduler) (Scheduler, Command) {
	next := s
	next.Inflight = s.Latest
	next.Cancelled = false
	return next, Command{Kind: CommandStartRender, Revision: next.Latest}
}
