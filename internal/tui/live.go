package tui

import (
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"time"

	"github.com/fsnotify/fsnotify"
	"github.com/gosuda/elegant-mermaid/internal/termgfx"
	"golang.org/x/term"
)

type terminalInput interface {
	Read(time.Duration) ([]byte, error)
	Close() error
}

type (
	renderResult struct{ state State }
	liveSession  struct {
		state                  State
		source                 []byte
		input                  terminalInput
		output                 io.Writer
		watcher                *fsnotify.Watcher
		absolute               string
		scheduler              Scheduler
		results                chan renderResult
		cancel                 context.CancelFunc
		finished               chan struct{}
		dirty                  bool
		changed, retry, escape time.Time
		keys                   []byte
		fd                     int
	}
)

func probe(terminal graphicsTerminal, mode termgfx.Mode) (termgfx.Mode, int, int, error) {
	if _, err := terminal.output.Write(termgfx.QueryBytes(terminal.environment)); err != nil {
		return mode, 8, 16, err
	}
	deadline := time.Now().Add(100 * time.Millisecond)
	var replies []byte
	for time.Now().Before(deadline) {
		chunk, err := terminal.input.Read(time.Until(deadline))
		if err != nil {
			return mode, 8, 16, err
		}
		if !time.Now().Before(deadline) {
			break
		}
		if len(replies)+len(chunk) > 65536 {
			return mode, 8, 16, fmt.Errorf("terminal probe reply exceeds limit")
		}
		replies = append(replies, chunk...)
		if da1Complete(replies) {
			break
		}
	}
	parsed := termgfx.ParseReplies(replies)
	if terminal.automatic {
		mode = termgfx.AutoMode(terminal.environment, parsed)
	}
	return mode, parsed.CellW, parsed.CellH, nil
}

type LiveConfig struct {
	Input     *os.File
	Output    io.Writer
	Automatic bool
	ProbeEnv  termgfx.Env
}

func Live(ctx context.Context, s State, src []byte, config LiveConfig) (err error) {
	in, out, automatic := config.Input, config.Output, config.Automatic
	fd := int(in.Fd())
	if automatic && !terminalPair(in, out) {
		s.Mode = termgfx.ModeCells
		automatic = false
	}
	var raw *term.State
	if term.IsTerminal(fd) {
		raw, err = term.MakeRaw(fd)
		if err != nil {
			return err
		}
		defer func() { err = errors.Join(err, term.Restore(fd, raw)) }()
	}
	reader, err := newTerminalInput(in)
	if err != nil {
		return err
	}
	defer func() { err = errors.Join(err, reader.Close()) }()
	if err = configureGraphics(&s, graphicsTerminal{fd: fd, raw: raw, input: reader, output: out, environment: config.ProbeEnv, automatic: automatic}); err != nil {
		return err
	}
	if _, err = io.WriteString(out, "\x1b[?1049h\x1b[?25l"); err != nil {
		return err
	}
	defer func() {
		_, e := io.WriteString(out, "\x1b_Ga=d,d=A,q=2\x1b\\\x1b[?25h\x1b[?1049l")
		err = errors.Join(err, e)
	}()
	watcher, absolute, err := watchInput(s.Path)
	if err != nil {
		return err
	}
	defer func() { err = errors.Join(err, watcher.Close()) }()
	setSourceBlocks(&s, src)
	session := liveSession{state: s, source: src, input: reader, output: out, watcher: watcher, absolute: absolute, results: make(chan renderResult, 1), dirty: true, fd: fd}
	defer session.stopRender()
	session.edited(ctx)
	return session.run(ctx)
}

func watchInput(path string) (*fsnotify.Watcher, string, error) {
	watcher, err := fsnotify.NewWatcher()
	if err != nil {
		return nil, "", err
	}
	absolute, err := filepath.Abs(path)
	if err != nil {
		return nil, "", errors.Join(err, watcher.Close())
	}
	if err = watcher.Add(filepath.Dir(absolute)); err != nil {
		return nil, "", errors.Join(err, watcher.Close())
	}
	return watcher, absolute, nil
}

type graphicsTerminal struct {
	fd          int
	raw         *term.State
	input       terminalInput
	output      io.Writer
	environment termgfx.Env
	automatic   bool
}

func configureGraphics(s *State, terminal graphicsTerminal) error {
	if terminal.raw == nil {
		return nil
	}
	if !terminal.automatic && !s.Mode.Pixel() {
		return nil
	}
	mode, cellW, cellH, err := probe(terminal, s.Mode)
	if err != nil {
		return err
	}
	s.Mode, s.CellW, s.CellH = mode, cellW, cellH
	if err = term.Restore(terminal.fd, terminal.raw); err != nil {
		return err
	}
	_, err = term.MakeRaw(terminal.fd)
	return err
}

func (session *liveSession) startRender(ctx context.Context) {
	renderCtx, cancel := context.WithCancel(ctx)
	session.cancel = cancel
	finished := make(chan struct{})
	session.finished = finished
	snapshot := session.state
	snapshot.Displayed = session.scheduler.Inflight
	src := session.source
	go func() {
		defer close(finished)
		result := Render(renderCtx, snapshot, src)
		session.results <- renderResult{state: result}
	}()
}

func (session *liveSession) stopRender() {
	if session.cancel == nil {
		return
	}
	session.cancel()
	<-session.finished
}

func (session *liveSession) edited(ctx context.Context) {
	next, cmd := Step(session.scheduler, EventEdited)
	session.scheduler = next
	session.applyCommand(ctx, cmd)
}

func (session *liveSession) applyCommand(ctx context.Context, cmd Command) {
	switch cmd.Kind {
	case CommandStartRender:
		session.startRender(ctx)
	case CommandCancelRender:
		session.cancel()
	}
}

func (session *liveSession) run(ctx context.Context) error {
	for {
		if err := ctx.Err(); err != nil {
			return err
		}
		if err := session.resize(); err != nil {
			return err
		}
		if err := session.event(ctx); err != nil {
			return err
		}
		session.watchTick(ctx)
		if session.dirty {
			if err := draw(session.output, session.state); err != nil {
				return err
			}
			session.dirty = false
		}
		quit, err := session.readKeys(ctx)
		if err != nil || quit {
			return err
		}
	}
}

func (session *liveSession) resize() error {
	if !term.IsTerminal(session.fd) {
		return nil
	}
	w, h, err := term.GetSize(session.fd)
	if err != nil {
		return err
	}
	w = max(20, w)
	h = max(5, h)
	if w != session.state.Width || h != session.state.Height {
		session.state.Resize(w, h)
		session.dirty = true
	}
	return nil
}

func (session *liveSession) event(ctx context.Context) error {
	select {
	case result := <-session.results:
		next, cmd := Step(session.scheduler, EventRenderDone)
		session.scheduler = next
		if cmd.Kind == CommandDisplay {
			session.display(result.state)
		} else {
			session.applyCommand(ctx, cmd)
		}
	case event, ok := <-session.watcher.Events:
		if !ok {
			return fmt.Errorf("file watcher closed")
		}
		name, err := filepath.Abs(event.Name)
		if err != nil {
			return err
		}
		if name == session.absolute {
			session.changed = time.Now()
		}
	case err, ok := <-session.watcher.Errors:
		if !ok {
			return fmt.Errorf("file watcher errors closed")
		}
		return err
	default:
	}
	return nil
}

func (session *liveSession) display(next State) {
	old := session.state
	next.Width = old.Width
	next.Height = old.Height
	next.OffsetX = old.OffsetX
	next.OffsetY = old.OffsetY
	next.Zoom = old.Zoom
	next.Fit = old.Fit
	if !old.AutoPanel && !next.AutoPanel {
		next.Panel = old.Panel
		next.AutoPanel = false
	}
	next.WatchLost = old.WatchLost
	next.FitImage()
	session.state = next
	session.dirty = true
}

func (session *liveSession) reload(ctx context.Context) {
	src, err := Read(session.state.Path)
	session.state.WatchLost = err != nil
	session.dirty = true
	if err != nil {
		return
	}
	session.source = src
	setSourceBlocks(&session.state, src)
	session.edited(ctx)
}

func (session *liveSession) watchTick(ctx context.Context) {
	now := time.Now()
	if !session.changed.IsZero() && now.Sub(session.changed) >= 50*time.Millisecond {
		session.changed = time.Time{}
		session.reload(ctx)
	}
	if session.state.WatchLost && !now.Before(session.retry) {
		session.retry = now.Add(500 * time.Millisecond)
		session.reload(ctx)
	}
}

func (session *liveSession) readKeys(ctx context.Context) (bool, error) {
	chunk, err := session.input.Read(10 * time.Millisecond)
	if err != nil {
		return false, err
	}
	if len(session.keys)+len(chunk) > 65536 {
		return false, fmt.Errorf("terminal key sequence exceeds limit")
	}
	session.keys = append(session.keys, chunk...)
	for len(session.keys) > 0 {
		key, used, pending := decodeKey(session.keys)
		if pending {
			if session.escape.IsZero() {
				session.escape = time.Now()
			}
			if time.Since(session.escape) < 50*time.Millisecond {
				break
			}
			key = "esc"
			used = 1
		}
		session.escape = time.Time{}
		session.keys = session.keys[used:]
		if session.applyKey(ctx, key) {
			return true, nil
		}
	}
	return false, nil
}

func (session *liveSession) applyKey(ctx context.Context, key string) bool {
	edit, quit := session.state.Key(key)
	if key == "r" {
		session.reload(ctx)
		edit = session.state.WatchLost
	}
	if edit {
		session.edited(ctx)
	}
	session.dirty = true
	return quit
}

func decodeKey(input []byte) (string, int, bool) {
	if input[0] == 3 {
		return "ctrl-c", 1, false
	}
	if input[0] != 27 {
		return string(input[:1]), 1, false
	}
	if len(input) == 1 {
		return "", 0, true
	}
	if input[1] != '[' {
		return "esc", 1, false
	}
	if len(input) < 3 {
		return "", 0, true
	}
	switch input[2] {
	case 'A':
		return "up", 3, false
	case 'B':
		return "down", 3, false
	case 'C':
		return "right", 3, false
	case 'D':
		return "left", 3, false
	}
	return "", 3, false
}

func terminalPair(in *os.File, out io.Writer) bool {
	output, ok := out.(*os.File)
	return ok && term.IsTerminal(int(in.Fd())) && term.IsTerminal(int(output.Fd()))
}
