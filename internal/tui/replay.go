package tui

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"unicode/utf8"

	"github.com/gosuda/elegant-mermaid/internal/fileerr"
)

var errInvalidUTF8 = errors.New("invalid UTF-8")

type replaySession struct {
	state     State
	source    []byte
	script    string
	scheduler Scheduler
}

func Replay(ctx context.Context, s State, src []byte, path string, out io.Writer) error {
	script, err := os.ReadFile(path)
	if err != nil {
		return fileerr.Read(path, err)
	}
	setSourceBlocks(&s, src)
	session := replaySession{state: s, source: src, script: path}
	session.send(EventEdited)
	if err = session.scan(ctx, script); err != nil {
		return err
	}
	session.settle(ctx)
	if err = ctx.Err(); err != nil {
		return err
	}
	_, err = io.WriteString(out, Frame(session.state))
	return err
}

func (session *replaySession) send(e Event) {
	next, _ := Step(session.scheduler, e)
	session.scheduler = next
}

func (session *replaySession) settle(ctx context.Context) {
	for session.scheduler.Inflight != 0 {
		if session.scheduler.Cancelled {
			session.send(EventRenderAborted)
			continue
		}
		session.state.Displayed = session.scheduler.Inflight
		session.state = Render(ctx, session.state, session.source)
		session.send(EventRenderDone)
	}
}

func (session *replaySession) scan(ctx context.Context, script []byte) error {
	for line := 1; len(script) > 0; line++ {
		var raw []byte
		raw, script, _ = bytes.Cut(script, []byte{'\n'})
		if !utf8.Valid(raw) {
			return fmt.Errorf("%s:%d: %w", session.script, line, errInvalidUTF8)
		}
		text := strings.TrimSpace(string(raw))
		if text == "" || strings.HasPrefix(text, "#") {
			continue
		}
		quit, err := session.event(ctx, text)
		if err != nil {
			return fmt.Errorf("%s:%d: %w", session.script, line, err)
		}
		if quit {
			return nil
		}
		if err = ctx.Err(); err != nil {
			return err
		}
	}
	return nil
}

func (session *replaySession) event(ctx context.Context, text string) (bool, error) {
	verb, arg, _ := strings.Cut(text, " ")
	arg = strings.TrimSpace(arg)
	switch verb {
	case "settle":
		return false, session.settleEvent(ctx, arg)
	case "file-delete":
		return false, session.deleteEvent(arg)
	case "file-change", "file-create":
		return false, session.sourceEvent(verb, arg)
	case "resize":
		return false, session.resizeEvent(arg)
	case "key":
		return session.keyEvent(arg)
	default:
		return false, fmt.Errorf("unknown verb %s", verb)
	}
}

func (session *replaySession) settleEvent(ctx context.Context, arg string) error {
	if arg != "" {
		return fmt.Errorf("settle takes no arguments")
	}
	session.settle(ctx)
	return nil
}

func (session *replaySession) deleteEvent(arg string) error {
	if arg != "" {
		return fmt.Errorf("file-delete takes no arguments")
	}
	session.state.WatchLost = true
	return nil
}

func (session *replaySession) sourceEvent(verb, arg string) error {
	if arg == "" {
		return fmt.Errorf("missing source path")
	}
	name := arg
	if !filepath.IsAbs(name) {
		name = filepath.Join(filepath.Dir(session.script), name)
	}
	src, err := Read(name)
	if err != nil {
		return err
	}
	session.source = src
	setSourceBlocks(&session.state, src)
	if verb == "file-create" {
		session.state.WatchLost = false
	}
	session.send(EventEdited)
	return nil
}

func (session *replaySession) resizeEvent(arg string) error {
	fields := strings.Fields(arg)
	if len(fields) != 2 {
		return fmt.Errorf("expected resize W H")
	}
	w, e1 := decimal(fields[0])
	h, e2 := decimal(fields[1])
	if e1 != nil || e2 != nil || w < 20 || h < 5 {
		return fmt.Errorf("size requires W >= 20 and H >= 5")
	}
	session.state.Resize(w, h)
	return nil
}

func (session *replaySession) keyEvent(key string) (bool, error) {
	if !validKey(key) {
		return false, fmt.Errorf("invalid key")
	}
	edit, quit := session.state.Key(key)
	if key == "r" {
		session.reload()
	}
	if edit {
		session.send(EventEdited)
	}
	return quit, nil
}

func (session *replaySession) reload() {
	src, err := Read(session.state.Path)
	session.state.WatchLost = err != nil
	if err != nil {
		return
	}
	session.source = src
	setSourceBlocks(&session.state, src)
}

func decimal(text string) (int, error) {
	for _, r := range text {
		if r < '0' || r > '9' {
			return 0, fmt.Errorf("invalid integer")
		}
	}
	return strconv.Atoi(text)
}

func validKey(text string) bool {
	if len(text) == 1 {
		return text[0] >= 33 && text[0] <= 126
	}
	switch text {
	case "up", "down", "left", "right", "esc", "ctrl-c":
		return true
	}
	return false
}
