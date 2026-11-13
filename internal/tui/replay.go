package tui

import (
	"bufio"
	"context"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"
)

type replaySession struct {
	state     State
	source    []byte
	script    string
	scheduler Scheduler
}

func Replay(ctx context.Context, s State, src []byte, path string, out io.Writer) (err error) {
	file, err := os.Open(path)
	if err != nil {
		return err
	}
	defer func() { err = errors.Join(err, file.Close()) }()
	setSourceBlocks(&s, src)
	session := replaySession{state: s, source: src, script: path}
	session.scheduler.Edit()
	if err = session.scan(ctx, file); err != nil {
		return err
	}
	session.settle(ctx)
	if err = ctx.Err(); err != nil {
		return err
	}
	_, err = io.WriteString(out, Frame(session.state))
	return err
}

func (session *replaySession) settle(ctx context.Context) {
	for session.scheduler.Inflight != 0 {
		if session.scheduler.Cancelled {
			session.scheduler.Done()
			continue
		}
		session.state.Displayed = session.scheduler.Inflight
		session.state = Render(ctx, session.state, session.source)
		session.scheduler.Done()
	}
}

func (session *replaySession) scan(ctx context.Context, input io.Reader) error {
	scanner := bufio.NewScanner(input)
	scanner.Buffer(make([]byte, 4096), 16*1024*1024)
	line := 0
	for scanner.Scan() {
		line++
		text := strings.TrimSpace(scanner.Text())
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
	if err := scanner.Err(); err != nil {
		return fmt.Errorf("%s:%d: %w", session.script, line, err)
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
	session.scheduler.Edit()
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
		session.scheduler.Edit()
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
