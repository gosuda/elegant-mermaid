package layout

import (
	"bytes"
	"errors"
	"fmt"

	"github.com/gosuda/elegant-mermaid/internal/scene"
	"github.com/gosuda/elegant-mermaid/internal/syntax"
)

var ErrSiteConfig = errors.New("invalid config")

func ParseSiteConfig(text []byte) (syntax.ConfigValue, error) {
	if len(bytes.TrimSpace(text)) == 0 {
		return syntax.ConfigValue{}, nil
	}
	value, ds := syntax.ParseConfigYAML(text, 0, len(text))
	if len(ds) != 0 {
		return syntax.ConfigValue{}, fmt.Errorf("%w: %s", ErrSiteConfig, ds[0].Message)
	}
	if value.Kind != syntax.ValueMapping {
		return syntax.ConfigValue{}, fmt.Errorf("%w: config must be a mapping", ErrSiteConfig)
	}
	if _, ds = syntax.ReadLook(value); len(ds) != 0 {
		return syntax.ConfigValue{}, fmt.Errorf("%w: %s", ErrSiteConfig, ds[0].Message)
	}
	return value, nil
}

func (d *Diagram) configMappings() []syntax.ConfigValue {
	var out []syntax.ConfigValue
	if d.Preprocessing.HasConfig {
		out = append(out, d.Preprocessing.Config)
	}
	if d.Preprocessing.HasInit {
		out = append(out, d.Preprocessing.Init)
	}
	return out
}

func (d *Diagram) Look(site syntax.ConfigValue) (scene.Look, error) {
	parsed, ds := d.look.Overlay(site)
	if len(ds) != 0 {
		return scene.Look{}, fmt.Errorf("%w: %s", ErrSiteConfig, ds[0].Message)
	}
	look := scene.Look{Seed: parsed.Seed}
	switch parsed.Value {
	case "neo":
		look.Kind = scene.LookNeo
	case "handDrawn":
		look.Kind = scene.LookHandDrawn
	}
	return look, nil
}
