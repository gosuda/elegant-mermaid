package layered

import (
	"errors"
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/scene"
)

var ErrTooLarge = errors.New("layout: model exceeds limits")

type LimitError struct {
	Resource      string
	Limit, Actual int64
}

func (e *LimitError) Error() string {
	return fmt.Sprintf("model exceeds the limit of %d; actual %d", e.Limit, e.Actual)
}
func (e *LimitError) Unwrap() error { return ErrTooLarge }
func enforceLimits(in Input, o scene.Options) error {
	limits := o.Limits
	defaults := scene.DefaultLimits()
	if limits.MaxNodes == 0 {
		limits.MaxNodes = defaults.MaxNodes
	}
	if limits.MaxEdges == 0 {
		limits.MaxEdges = defaults.MaxEdges
	}
	if limits.MaxTextBytes == 0 {
		limits.MaxTextBytes = defaults.MaxTextBytes
	}
	textBytes, err := inputTextBytes(in)
	if err != nil {
		return err
	}
	counts := []struct {
		name          string
		actual, limit int64
	}{
		{"nodes", int64(len(in.Boxes)), int64(limits.MaxNodes)},
		{"edges", int64(len(in.Routes)), int64(limits.MaxEdges)},
		{"text bytes", textBytes, int64(limits.MaxTextBytes)},
	}
	for _, c := range counts {
		if c.limit < 0 || c.actual < 0 {
			return ErrGraph
		}
		if c.actual > c.limit {
			return &LimitError{Resource: c.name, Limit: c.limit, Actual: c.actual}
		}
	}
	return ValidateOwners(in.Boxes, in.Routes)
}

func inputTextBytes(in Input) (int64, error) {
	var total int64
	add := func(text string) error {
		if int64(len(text)) > int64(^uint64(0)>>1)-total {
			return ErrTooLarge
		}
		total += int64(len(text))
		return nil
	}
	for i := range in.Boxes {
		text := inputBoxText(in, i)
		if err := add(text); err != nil {
			return 0, err
		}
	}
	for _, l := range in.Labels {
		if subOwner(in, l.Owner) {
			if err := add(l.Text); err != nil {
				return 0, err
			}
		}
	}
	return total, nil
}
